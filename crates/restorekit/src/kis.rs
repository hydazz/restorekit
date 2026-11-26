//! Identity of a Mac in DFU over Apple's Debug USB interface ("KIS", `05ac:1881`).
//!
//! A KIS-mode Mac is in the same bootrom DFU as a classic `05ac:1227` one, but its
//! USB serial is empty: the `CPID:… BDID:… ECID:…` string sits behind a KIS
//! request instead. This is a port of libirecovery's `irecv_kis_init` +
//! `irecv_kis_load_device_info` over nusb, so we can open exactly the device we
//! enumerated (libirecovery's `irecv_open_with_ecid(0)` takes whichever
//! restore-family device it finds first).
//!
//! macOS gates `05ac:1881` behind the `com.apple.private.debug-usb.access`
//! entitlement, which only Apple's `deviceinterfaced` holds. The daemon hands a
//! raw KIS transport to any client through the private
//! `DeviceInterfaceClient.framework`, so on macOS the same request goes through
//! it instead (see [`dic`]). The vendored libirecovery is patched the same way
//! for the restore itself (`restorekit-sys/patches/libirecovery`).

use std::collections::HashMap;
#[cfg(not(target_os = "macos"))]
use std::io;
use std::sync::{Mutex, OnceLock};
use std::time::{Duration, Instant};

#[cfg(not(target_os = "macos"))]
use nusb::transfer::{Buffer, Bulk, Completion, In, Out, TransferError};
use nusb::MaybeFuture;

/// The config portal, on bulk endpoints 0x01 and 0x81.
pub const PORTAL_CONFIG: u8 = 0x01;
/// The RSM portal, on bulk endpoints 0x03 and 0x83.
pub const PORTAL_RSM: u8 = 0x10;
/// Read registers: the request command a request word starts with.
pub const READ_REGISTERS: u32 = 0;
/// Write registers.
pub const WRITE_REGISTERS: u32 = 1;
/// Read memory.
pub const READ_MEMORY: u32 = 2;
/// Write memory.
pub const WRITE_MEMORY: u32 = 3;

#[cfg_attr(target_os = "macos", allow(dead_code))]
const INDEX_ENABLE_A: u16 = 0x0a;
#[cfg_attr(target_os = "macos", allow(dead_code))]
const INDEX_ENABLE_B: u16 = 0x14;
const INDEX_GET_INFO: u16 = 0x100;
#[cfg_attr(target_os = "macos", allow(dead_code))]
const ENABLE_A: u32 = 0x21;
#[cfg_attr(target_os = "macos", allow(dead_code))]
const ENABLE_B: u32 = 0x01;

const HEADER_LEN: usize = 12;
/// A reply's trailer: the bytes the device moved and its status.
#[cfg_attr(target_os = "macos", allow(dead_code))]
const TRAILER_LEN: usize = 8;
/// The most one memory request carries.
#[cfg_attr(target_os = "macos", allow(dead_code))]
const MAX_MEMORY: usize = 0x10000;
/// Size of the device-info block the GET_INFO reply carries after its header.
const INFO_LEN: usize = 0x300;
/// Offset of the embedded USB device descriptor inside the info block.
const DESCRIPTOR_OFFSET: usize = 64;
/// `iSerialNumber` within a USB device descriptor.
const I_SERIAL_NUMBER: usize = 16;
/// Word offset of the nonce string, inside the info block.
const NONCE_OFFSET: usize = 24;

#[cfg_attr(target_os = "macos", allow(dead_code))]
const TIMEOUT: Duration = Duration::from_secs(2);

/// What a Debug USB device answered to GET_INFO.
#[derive(Debug, Clone, PartialEq)]
pub enum Read {
    /// In DFU: the identity string (`CPID:… ECID:…`).
    Serial(String),
    /// It answered, but with no info block: the chip isn't in DFU (e.g. a
    /// booted device with Debug USB switched on at its port), so there's no
    /// identity to read.
    NotInDfu,
    /// The request itself failed.
    Failed,
}

/// How long after a KIS device first shows up a failed read is retried right
/// away. On macOS `deviceinterfaced` attaches to the device on the same
/// arrival, so the first request can land before it's ready.
const ARRIVAL_GRACE: Duration = Duration::from_secs(3);

/// One arrival of a device on the bus. The device id alone already changes
/// with each arrival on macOS (a registry entry id) and Linux (bus and
/// address). Windows keeps the device instance, and so the id, for whatever
/// arrives at the same port, and may hand out the same bus address again, so
/// add the time Windows recorded this arrival.
type Arrival = (nusb::DeviceId, u64);

/// When each KIS device was first seen, and its identity once read.
type Seen = HashMap<Arrival, (Instant, Option<String>)>;

/// `None` when Windows won't say when the device arrived: its identity then
/// isn't cached, rather than risk handing it to the next Mac at that port.
fn arrival(info: &nusb::DeviceInfo) -> Option<Arrival> {
    #[cfg(target_os = "windows")]
    return Some((info.id(), last_arrival(info)?));
    #[cfg(not(target_os = "windows"))]
    Some((info.id(), 0))
}

/// The FILETIME of the device's last arrival, which the PnP manager records.
#[cfg(target_os = "windows")]
fn last_arrival(info: &nusb::DeviceInfo) -> Option<u64> {
    use std::os::windows::ffi::OsStrExt;
    use windows_sys::Win32::Devices::DeviceAndDriverInstallation::{
        CM_Get_DevNode_PropertyW, CM_Locate_DevNodeW, CM_LOCATE_DEVNODE_NORMAL, CR_SUCCESS,
    };
    use windows_sys::Win32::Devices::Properties::{
        DEVPKEY_Device_LastArrivalDate, DEVPROP_TYPE_FILETIME,
    };

    let id: Vec<u16> = info.instance_id().encode_wide().chain([0]).collect();
    unsafe {
        let mut dev = 0;
        if CM_Locate_DevNodeW(&mut dev, id.as_ptr(), CM_LOCATE_DEVNODE_NORMAL) != CR_SUCCESS {
            return None;
        }
        let mut kind = 0;
        let mut buf = [0u8; 8];
        let mut size = buf.len() as u32;
        let ok = CM_Get_DevNode_PropertyW(
            dev,
            &DEVPKEY_Device_LastArrivalDate,
            &mut kind,
            buf.as_mut_ptr(),
            &mut size,
            0,
        ) == CR_SUCCESS;
        (ok && kind == DEVPROP_TYPE_FILETIME && size == 8).then(|| u64::from_le_bytes(buf))
    }
}

fn seen() -> &'static Mutex<Seen> {
    static SEEN: OnceLock<Mutex<Seen>> = OnceLock::new();
    SEEN.get_or_init(Default::default)
}

/// Drop what [`identify`] remembers about devices no longer on the bus.
pub(crate) fn forget_absent(present: &[nusb::DeviceId]) {
    seen()
        .lock()
        .unwrap()
        .retain(|(id, _), _| present.contains(id));
}

/// Read the KIS device behind `info`. A good identity is cached per arrival,
/// so polling `list()` asks each device once; anything else is asked again on
/// the next call, so a device that finishes coming up (or a daemon that
/// finishes attaching) isn't stuck with its first answer.
pub(crate) fn identify(info: &nusb::DeviceInfo) -> Read {
    let seen = seen();
    let arrival = arrival(info);
    let first_seen = match arrival {
        Some(arrival) => {
            let mut seen = seen.lock().unwrap();
            let entry = seen.entry(arrival).or_insert((Instant::now(), None));
            if let Some(serial) = &entry.1 {
                return Read::Serial(serial.clone());
            }
            entry.0
        }
        None => Instant::now(),
    };
    let read = loop {
        let read = read(info);
        if read != Read::Failed || first_seen.elapsed() >= ARRIVAL_GRACE {
            break read;
        }
        std::thread::sleep(Duration::from_millis(250));
    };
    if let (Read::Serial(serial), Some(arrival)) = (&read, arrival) {
        seen.lock()
            .unwrap()
            .insert(arrival, (first_seen, Some(serial.clone())));
    }
    read
}

fn read(info: &nusb::DeviceInfo) -> Read {
    #[cfg(target_os = "windows")]
    if info
        .driver()
        .is_some_and(|d| d.eq_ignore_ascii_case("AppleKIS"))
    {
        return apple_kis::read(info);
    }
    #[cfg(target_os = "macos")]
    match claim::held(info.location_id()) {
        // Held, but its holder hasn't written the identity yet.
        Some(serial) if serial.is_empty() => return Read::Failed,
        Some(serial) => return Read::Serial(serial),
        None => {}
    }
    match get_info(info) {
        Ok(block) => parse_info(&block),
        Err(_) => Read::Failed,
    }
}

/// What a GET_INFO block says: the 0x300-byte info block of a chip in DFU,
/// whose `aDFU` identity carries the serial; anything shorter, such as the
/// nothing a booted device with Debug USB on answers, means it has none.
pub fn parse_info(block: &[u8]) -> Read {
    if block.len() < INFO_LEN {
        return Read::NotInDfu;
    }
    match serial_from_info(block) {
        Some(serial) => Read::Serial(serial),
        None => Read::Failed,
    }
}

/// The GET_INFO block for the device.
#[cfg(not(target_os = "macos"))]
fn get_info(info: &nusb::DeviceInfo) -> Result<Vec<u8>, String> {
    let mut kis = Kis::open(info).map_err(|e| e.to_string())?;
    kis.get_info().map_err(|e| format!("GET_INFO: {e}"))
}

/// The GET_INFO block, through `deviceinterfaced`. It enables the device
/// itself when it attaches, so there's no config write here.
#[cfg(target_os = "macos")]
fn get_info(info: &nusb::DeviceInfo) -> Result<Vec<u8>, String> {
    let id = dic::interface_for(info.registry_entry_id())?;
    let req = header(
        0,
        PORTAL_RSM,
        request_word(READ_REGISTERS, INDEX_GET_INFO, INFO_LEN / 4),
        0,
    );
    let reply = dic::request(id, &req, HEADER_LEN + INFO_LEN + TRAILER_LEN)?;
    // The header, the block, then the trailer.
    Ok(reply
        .get(HEADER_LEN..reply.len().saturating_sub(TRAILER_LEN))
        .unwrap_or_default()
        .to_vec())
}

/// Which Mac in DFU over Debug USB each restore on this host is working on.
///
/// `deviceinterfaced` hands the same KIS device to every process that asks, and
/// a KIS device's identity can only be read by sending it a request. One that
/// lands between another restore's transfers fails, or breaks them. So a
/// restore holds a lock on a file named for its Mac's IOKit `locationID` and
/// leaves the Mac's identity in it. Another process reads the identity from
/// the file instead of from the Mac ([`identify`]), and libirecovery in it is
/// kept from opening the Mac ([`install`]).
#[cfg(target_os = "macos")]
pub(crate) mod claim {
    use std::fs::File;
    use std::io::{Read as _, Write as _};
    use std::os::raw::c_int;
    use std::sync::{Mutex, Once};

    use restorekit_sys as sys;

    use crate::{lock, Error, Result};

    /// The location of the Mac this process's restore holds, and its lock
    /// (`None` when the lock file couldn't be had).
    static HELD: Mutex<Option<(u32, Option<File>)>> = Mutex::new(None);

    fn own() -> Option<u32> {
        HELD.lock().unwrap().as_ref().map(|(location, _)| *location)
    }

    fn name(location: u32) -> String {
        format!("kis-{location:08x}")
    }

    /// The identity of the Mac at `location` when another process's restore
    /// holds it, as that restore read it (empty until it has written it).
    /// `None` when no other process holds that location.
    pub(crate) fn held(location: u32) -> Option<String> {
        if own() == Some(location) {
            return None;
        }
        let mut file = lock::held(&name(location))?;
        let mut serial = String::new();
        let _ = file.read_to_string(&mut serial);
        Some(serial)
    }

    /// A restore of a Mac in DFU over Debug USB has no use for any other KIS
    /// device. Anything else keeps off the ones other restores hold.
    extern "C" fn excluded(location: u32) -> c_int {
        c_int::from(match own() {
            Some(own) => location != own,
            None => held(location).is_some(),
        })
    }

    /// Have libirecovery pass over, unopened, each KIS device this process is
    /// to keep off. Call before anything that has it open devices by ECID or
    /// watch for them: either opens every KIS device to read its ECID.
    pub(crate) fn install() {
        static INSTALLED: Once = Once::new();
        INSTALLED.call_once(|| unsafe {
            sys::irecv_set_kis_filter(Some(excluded));
        });
    }

    /// Held for the length of a restore; see [`hold`].
    pub(crate) struct Claim(());

    impl Drop for Claim {
        fn drop(&mut self) {
            *HELD.lock().unwrap() = None;
        }
    }

    /// Take the Mac with `ecid` for this process's restore, if it's in DFU
    /// over Debug USB, until the claim drops: other processes keep off it, and
    /// libirecovery here opens no other KIS device. `None` for a target in any
    /// other mode. Fails when another restore holds that Mac.
    pub(crate) fn hold(ecid: u64) -> Result<Option<Claim>> {
        use nusb::MaybeFuture;
        install();
        let target = nusb::list_devices()
            .wait()
            .map_err(Error::from)?
            .filter(|i| {
                i.vendor_id() == crate::device::APPLE_VID
                    && i.product_id() == crate::device::KIS_PID
            })
            .find_map(|i| match super::identify(&i) {
                super::Read::Serial(serial)
                    if crate::device::parse_serial(&serial).is_some_and(|p| p.2 == ecid) =>
                {
                    Some((i.location_id(), serial))
                }
                _ => None,
            });
        let Some((location, serial)) = target else {
            return Ok(None);
        };
        let file = lock::take(&name(location)).map_err(|_| Error::RestoreInProgress(ecid))?;
        if let Some(mut file) = file.as_ref() {
            file.set_len(0)
                .and_then(|()| file.write_all(serial.as_bytes()))
                .map_err(|e| Error::Usb(format!("lock for {ecid:#x}: {e}")))?;
        }
        *HELD.lock().unwrap() = Some((location, file));
        Ok(Some(Claim(())))
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn another_holder_leaves_the_identity_it_read() {
            let location = 0xfff0_0000 | (std::process::id() & 0xffff);
            assert_eq!(held(location), None);
            let mut file = lock::take(&name(location)).unwrap().unwrap();
            assert_eq!(held(location).as_deref(), Some(""));
            assert_eq!(excluded(location), 1);
            *HELD.lock().unwrap() = Some((location + 1, None));
            assert_eq!((excluded(location), excluded(location + 1)), (1, 0));
            *HELD.lock().unwrap() = None;
            file.write_all(b"CPID:8103 ECID:000C60A812345678").unwrap();
            assert_eq!(
                held(location).as_deref(),
                Some("CPID:8103 ECID:000C60A812345678")
            );
            drop(file);
            assert_eq!(held(location), None);
            assert_eq!(excluded(location), 0);
            std::fs::remove_file(format!("/tmp/restorekit-{}.lock", name(location))).unwrap();
        }
    }
}

/// A readable dump of every KIS device on the bus: what `deviceinterfaced` sees
/// (macOS), the raw GET_INFO reply and what it parses to. For checking the
/// transport on real hardware; prints nothing it can't read rather than failing.
pub fn probe() -> String {
    use std::fmt::Write;
    let mut out = String::new();
    #[cfg(target_os = "macos")]
    dic::describe(&mut out);
    let devices: Vec<_> = match nusb::list_devices().wait() {
        Ok(d) => d
            .filter(|d| {
                d.vendor_id() == crate::device::APPLE_VID
                    && d.product_id() == crate::device::KIS_PID
            })
            .collect(),
        Err(e) => {
            let _ = writeln!(out, "list USB devices: {e}");
            return out;
        }
    };
    if devices.is_empty() {
        let _ = writeln!(out, "no 05ac:1881 device on the bus");
    }
    for info in &devices {
        let _ = writeln!(out, "\n05ac:1881 {:?}", info.id());
        #[cfg(target_os = "macos")]
        let _ = writeln!(out, "  registry entry id {:#x}", info.registry_entry_id());
        match get_info(info) {
            Ok(block) => {
                let _ = writeln!(out, "  GET_INFO block, {} bytes:", block.len());
                hexdump(&mut out, &block);
                let _ = writeln!(out, "  reads as: {:?}", parse_info(&block));
                let _ = writeln!(out, "  serial: {:?}", serial_from_info(&block));
                let _ = writeln!(out, "  nonces: {:?}", nonces_from_info(&block));
            }
            Err(e) => {
                let _ = writeln!(out, "  GET_INFO failed: {e}");
            }
        }
    }
    out
}

fn hexdump(out: &mut String, bytes: &[u8]) {
    use std::fmt::Write;
    for (i, row) in bytes.chunks(16).enumerate() {
        let hex: Vec<String> = row.iter().map(|b| format!("{b:02x}")).collect();
        let text: String = row
            .iter()
            .map(|&b| {
                if (0x20..0x7f).contains(&b) {
                    b as char
                } else {
                    '.'
                }
            })
            .collect();
        let _ = writeln!(out, "    {:04x}: {:<47}  {text}", i * 16, hex.join(" "));
    }
}

/// AppleKIS's GET_INFO reply: vid, pid, a word, then four 255-byte strings
/// (nonces, serial, manufacturer, product), as libirecovery declares it.
#[cfg(any(target_os = "windows", test))]
const APPLE_KIS_FIELD: usize = 255;
#[cfg(any(target_os = "windows", test))]
const APPLE_KIS_SERIAL_OFFSET: usize = 8 + APPLE_KIS_FIELD;
#[cfg(any(target_os = "windows", test))]
const APPLE_KIS_SERIAL_END: usize = APPLE_KIS_SERIAL_OFFSET + APPLE_KIS_FIELD;
#[cfg(any(target_os = "windows", test))]
const APPLE_KIS_INFO_SIZE: usize = 8 + 4 * APPLE_KIS_FIELD;

/// The identity string out of an AppleKIS GET_INFO reply. An empty serial
/// means the chip behind the port isn't in DFU.
#[cfg(any(target_os = "windows", test))]
fn classify_apple_kis(reply: &[u8]) -> Read {
    let Some(field) = reply.get(APPLE_KIS_SERIAL_OFFSET..APPLE_KIS_SERIAL_END) else {
        return Read::Failed;
    };
    let end = field.iter().position(|&b| b == 0).unwrap_or(field.len());
    let serial = String::from_utf8_lossy(&field[..end]).trim().to_string();
    if serial.is_empty() {
        Read::NotInDfu
    } else {
        Read::Serial(serial)
    }
}

/// Windows with Apple's own AppleKIS driver bound (Windows Update installs it
/// with the first Apple device). AppleKIS enables the device itself and exposes
/// it as a `KIS\VID_05AC&PID_0001` child that answers a GET_INFO ioctl with the
/// identity string, the way libirecovery's Windows backend reads it. A device
/// that AppleKIS failed to enable has no such child until it re-enters DFU.
#[cfg(target_os = "windows")]
mod apple_kis {
    use std::os::windows::ffi::OsStrExt;
    use std::ptr::{null, null_mut};

    use windows_sys::core::GUID;
    use windows_sys::Win32::Devices::DeviceAndDriverInstallation::{
        CM_Get_Child, CM_Get_Device_IDW, CM_Get_Device_Interface_ListW,
        CM_Get_Device_Interface_List_SizeW, CM_Locate_DevNodeW,
        CM_GET_DEVICE_INTERFACE_LIST_PRESENT, CM_LOCATE_DEVNODE_NORMAL, CR_SUCCESS,
    };
    use windows_sys::Win32::Foundation::{
        CloseHandle, GetLastError, ERROR_IO_PENDING, GENERIC_READ, GENERIC_WRITE,
        INVALID_HANDLE_VALUE, WAIT_OBJECT_0,
    };
    use windows_sys::Win32::Storage::FileSystem::{
        CreateFileW, FILE_FLAG_OVERLAPPED, FILE_SHARE_READ, FILE_SHARE_WRITE, OPEN_EXISTING,
    };
    use windows_sys::Win32::System::Threading::{CreateEventW, WaitForSingleObject};
    use windows_sys::Win32::System::IO::{
        CancelIo, DeviceIoControl, GetOverlappedResult, OVERLAPPED,
    };

    use super::Read;

    use super::{classify_apple_kis, APPLE_KIS_INFO_SIZE as INFO_SIZE, APPLE_KIS_SERIAL_END};

    const GUID_DEVINTERFACE_KIS: GUID = GUID::from_u128(0xb36f4137_f4ef_4bfc_a25a_c2410768ee37);
    const IOCTL_GET_INFO: u32 = 0x220004;

    pub(super) fn read(info: &nusb::DeviceInfo) -> Read {
        match get_info(info) {
            Some(reply) => classify_apple_kis(&reply),
            None => Read::Failed,
        }
    }

    /// The KIS interface path of the AppleKIS child under `info`.
    fn interface_path(info: &nusb::DeviceInfo) -> Option<Vec<u16>> {
        let id: Vec<u16> = info.instance_id().encode_wide().chain([0]).collect();
        unsafe {
            let mut dev = 0;
            if CM_Locate_DevNodeW(&mut dev, id.as_ptr(), CM_LOCATE_DEVNODE_NORMAL) != CR_SUCCESS {
                return None;
            }
            let mut child = 0;
            if CM_Get_Child(&mut child, dev, 0) != CR_SUCCESS {
                return None;
            }
            let mut child_id = [0u16; 512];
            if CM_Get_Device_IDW(child, child_id.as_mut_ptr(), child_id.len() as u32, 0)
                != CR_SUCCESS
            {
                return None;
            }
            let mut len = 0;
            if CM_Get_Device_Interface_List_SizeW(
                &mut len,
                &GUID_DEVINTERFACE_KIS,
                child_id.as_ptr(),
                CM_GET_DEVICE_INTERFACE_LIST_PRESENT,
            ) != CR_SUCCESS
            {
                return None;
            }
            let mut list = vec![0u16; len as usize];
            if CM_Get_Device_Interface_ListW(
                &GUID_DEVINTERFACE_KIS,
                child_id.as_ptr(),
                list.as_mut_ptr(),
                len,
                CM_GET_DEVICE_INTERFACE_LIST_PRESENT,
            ) != CR_SUCCESS
            {
                return None;
            }
            let end = list.iter().position(|&c| c == 0).filter(|&e| e > 0)?;
            list.truncate(end + 1);
            Some(list)
        }
    }

    fn get_info(info: &nusb::DeviceInfo) -> Option<Vec<u8>> {
        let path = interface_path(info)?;
        let timeout_ms = super::TIMEOUT.as_millis() as u32;
        unsafe {
            let handle = CreateFileW(
                path.as_ptr(),
                GENERIC_READ | GENERIC_WRITE,
                FILE_SHARE_READ | FILE_SHARE_WRITE,
                null(),
                OPEN_EXISTING,
                FILE_FLAG_OVERLAPPED,
                null_mut(),
            );
            if handle == INVALID_HANDLE_VALUE {
                return None;
            }
            let mut reply = vec![0u8; INFO_SIZE];
            let mut ov: OVERLAPPED = std::mem::zeroed();
            ov.hEvent = CreateEventW(null(), 1, 0, null());
            let mut got = 0u32;
            let mut ok = !ov.hEvent.is_null()
                && DeviceIoControl(
                    handle,
                    IOCTL_GET_INFO,
                    null(),
                    0,
                    reply.as_mut_ptr().cast(),
                    INFO_SIZE as u32,
                    null_mut(),
                    &mut ov,
                ) != 0;
            if !ok && !ov.hEvent.is_null() && GetLastError() == ERROR_IO_PENDING {
                if WaitForSingleObject(ov.hEvent, timeout_ms) != WAIT_OBJECT_0 {
                    CancelIo(handle);
                }
                ok = GetOverlappedResult(handle, &ov, &mut got, 1) != 0;
            } else if ok {
                GetOverlappedResult(handle, &ov, &mut got, 0);
            }
            if !ov.hEvent.is_null() {
                CloseHandle(ov.hEvent);
            }
            CloseHandle(handle);
            (ok && got as usize >= APPLE_KIS_SERIAL_END).then_some(reply)
        }
    }
}

/// One claimed KIS interface, with its config and RSM portals. Replies are
/// matched to requests by sequence number, so every request to a device goes
/// through the one holder of this. A request ends only at a short packet, so
/// one that fills its last packet is followed by an empty one.
#[cfg(not(target_os = "macos"))]
pub struct Kis {
    _interface: nusb::Interface,
    config: (nusb::Endpoint<Bulk, Out>, nusb::Endpoint<Bulk, In>),
    rsm: (nusb::Endpoint<Bulk, Out>, nusb::Endpoint<Bulk, In>),
    seq: u16,
}

/// A reply's data, then how many bytes the device moved and its status.
#[cfg(not(target_os = "macos"))]
#[derive(Debug)]
pub struct Reply {
    pub data: Vec<u8>,
    pub size: u32,
    pub status: u32,
}

#[cfg(not(target_os = "macos"))]
fn done(completion: Completion) -> io::Result<Completion> {
    match completion.status {
        Ok(()) => Ok(completion),
        Err(TransferError::Cancelled) => Err(io::Error::new(
            io::ErrorKind::TimedOut,
            "Debug USB stopped answering",
        )),
        Err(TransferError::Disconnected) => Err(io::Error::new(
            io::ErrorKind::NotConnected,
            "Debug USB left",
        )),
        Err(error) => Err(error.into()),
    }
}

#[cfg(not(target_os = "macos"))]
impl Kis {
    /// Claim the device's KIS interface and enable it, as libirecovery does.
    pub fn open(info: &nusb::DeviceInfo) -> io::Result<Self> {
        let device = info.open().wait()?;
        if device
            .active_configuration()
            .map_or(true, |config| config.configuration_value() != 1)
        {
            device.set_configuration(1).wait()?;
        }
        let interface = device.claim_interface(0).wait()?;
        let pair = |number| -> io::Result<_> {
            Ok((
                interface.endpoint::<Bulk, Out>(number)?,
                interface.endpoint::<Bulk, In>(number | 0x80)?,
            ))
        };
        let mut kis = Self {
            config: pair(0x01)?,
            rsm: pair(0x03)?,
            _interface: interface,
            seq: 0,
        };
        kis.write_config(INDEX_ENABLE_A, ENABLE_A)?;
        kis.write_config(INDEX_ENABLE_B, ENABLE_B)?;
        Ok(kis)
    }

    /// Send a request to a portal and wait for its reply of up to `reply`
    /// bytes of data. A reply to an earlier request that timed out is passed
    /// over.
    pub fn request(
        &mut self,
        portal: u8,
        request: u32,
        args: &[u8],
        reply: usize,
    ) -> io::Result<Reply> {
        self.seq = self.seq.wrapping_add(1);
        let seq = self.seq;
        let mut message = header(seq, portal, request, args.len()).to_vec();
        message.extend_from_slice(args);
        let (out, inp) = if portal == PORTAL_CONFIG {
            &mut self.config
        } else {
            &mut self.rsm
        };
        let length = message.len();
        let sent = done(out.transfer_blocking(message.into(), TIMEOUT))?;
        if sent.actual_len != length {
            return Err(io::Error::other("Debug USB took part of a request"));
        }
        if length.is_multiple_of(out.max_packet_size()) {
            done(out.transfer_blocking(Buffer::new(0), TIMEOUT))?;
        }
        let packet = inp.max_packet_size().max(1);
        let want = (HEADER_LEN + reply + TRAILER_LEN).div_ceil(packet) * packet;
        loop {
            let reply = done(inp.transfer_blocking(Buffer::new(want), TIMEOUT))?.buffer;
            let n = reply.len();
            if n >= HEADER_LEN + TRAILER_LEN
                && reply[3] == portal
                && reply[..2] == seq.to_le_bytes()
            {
                let word = |at: usize| u32::from_le_bytes(reply[at..at + 4].try_into().unwrap());
                return Ok(Reply {
                    size: word(n - 8),
                    status: word(n - 4),
                    data: reply[HEADER_LEN..n - TRAILER_LEN].to_vec(),
                });
            }
        }
    }

    pub fn write_config(&mut self, index: u16, value: u32) -> io::Result<()> {
        self.request(
            PORTAL_CONFIG,
            request_word(WRITE_REGISTERS, index, 1),
            &value.to_le_bytes(),
            0,
        )?;
        Ok(())
    }

    /// Write one RSM register; the reply says how many bytes it took.
    pub fn write_register(&mut self, index: u16, value: u32) -> io::Result<u32> {
        let reply = self.request(
            PORTAL_RSM,
            request_word(WRITE_REGISTERS, index, 1),
            &value.to_le_bytes(),
            0,
        )?;
        Ok(reply.size)
    }

    /// Read RSM registers. A device whose RSM side is not up returns fewer.
    pub fn read_registers(&mut self, index: u16, count: usize) -> io::Result<Vec<u32>> {
        let reply = self.request(
            PORTAL_RSM,
            request_word(READ_REGISTERS, index, count),
            &[],
            4 * count,
        )?;
        Ok(reply.data.as_chunks::<4>().0[..]
            .iter()
            .take(count)
            .map(|word| u32::from_le_bytes(*word))
            .collect())
    }

    /// The GET_INFO block: registers 0x100 on, empty when there is none.
    pub fn get_info(&mut self) -> io::Result<Vec<u8>> {
        Ok(self
            .read_registers(INDEX_GET_INFO, INFO_LEN / 4)?
            .into_iter()
            .flat_map(u32::to_le_bytes)
            .collect())
    }

    /// Read `len` bytes of memory in address space `space`.
    pub fn read_memory(&mut self, space: u32, address: u64, len: usize) -> io::Result<Vec<u8>> {
        let mut data = self.memory(space, false, address, &[], len)?;
        data.truncate(len);
        Ok(data)
    }

    /// Write memory in address space `space`, in requests the device takes.
    pub fn write_memory(&mut self, space: u32, address: u64, data: &[u8]) -> io::Result<()> {
        for (offset, chunk) in (0..).step_by(MAX_MEMORY).zip(data.chunks(MAX_MEMORY)) {
            self.memory(space, true, address + offset, chunk, chunk.len())?;
        }
        Ok(())
    }

    fn memory(
        &mut self,
        space: u32,
        write: bool,
        address: u64,
        data: &[u8],
        len: usize,
    ) -> io::Result<Vec<u8>> {
        let mut args = Vec::with_capacity(12 + data.len());
        args.extend_from_slice(&address.to_le_bytes());
        args.extend_from_slice(&u32::try_from(len).map_err(io::Error::other)?.to_le_bytes());
        args.extend_from_slice(data);
        let command = if write { WRITE_MEMORY } else { READ_MEMORY };
        let reply = self.request(
            PORTAL_RSM,
            command | space << 8,
            &args,
            if write { 0 } else { len },
        )?;
        if reply.size as usize != len || (!write && reply.data.len() < len) {
            return Err(io::Error::other(format!(
                "Debug USB moved {} of {len} bytes at {address:#x} (status {:#x})",
                reply.size, reply.status
            )));
        }
        Ok(reply.data)
    }
}

/// The 12-byte KIS request header (libirecovery's `irecv_kis_request_init`):
/// sequence, protocol version 0xa0, portal, the request word and the length
/// of the arguments that follow.
fn header(seq: u16, portal: u8, request: u32, args_len: usize) -> [u8; HEADER_LEN] {
    let mut h = [0u8; HEADER_LEN];
    h[0..2].copy_from_slice(&seq.to_le_bytes());
    h[2] = 0xa0;
    h[3] = portal;
    h[4..8].copy_from_slice(&request.to_le_bytes());
    h[8..12].copy_from_slice(&(args_len as u32).to_le_bytes());
    h
}

/// A register request word: the command, the first register and how many.
pub fn request_word(command: u32, index: u16, count: usize) -> u32 {
    command | u32::from(index) << 8 | (count as u32) << 18
}

/// Pull the serial string out of a GET_INFO info block: the embedded device
/// descriptor's `iSerialNumber` is a word offset to a USB string descriptor.
fn serial_from_info(info: &[u8]) -> Option<String> {
    let index = *info.get(DESCRIPTOR_OFFSET + I_SERIAL_NUMBER)? as usize;
    string_at(info, index * 4)
}

/// The `NONC:… SNON:…` string, at the word offset stored at `NONCE_OFFSET`.
fn nonces_from_info(info: &[u8]) -> Option<String> {
    let word = u32::from_le_bytes(info.get(NONCE_OFFSET..NONCE_OFFSET + 4)?.try_into().ok()?);
    string_at(info, word as usize * 4)
}

/// A USB string descriptor (`bLength`, `bDescriptorType` = 3, UTF-16LE) at `off`.
/// `bLength` counts the two header bytes.
fn string_at(info: &[u8], off: usize) -> Option<String> {
    let len = *info.get(off)? as usize;
    if *info.get(off + 1)? != 3 || len < 2 || !len.is_multiple_of(2) {
        return None;
    }
    let units: Vec<u16> = info
        .get(off + 2..off + len)?
        .as_chunks::<2>()
        .0
        .iter()
        .map(|c| u16::from_le_bytes(*c))
        .collect();
    let s = String::from_utf16(&units).ok()?;
    (!s.is_empty()).then_some(s)
}

/// The KIS transport `deviceinterfaced` exposes through
/// `DeviceInterfaceClient.framework`. The framework is private and undocumented;
/// these signatures come from disassembling it and were checked against a live
/// Debug USB device (an iPhone with Debug USB enabled over USB-PD): listing,
/// portal-to-endpoint mapping and a GET_INFO round trip.
#[cfg(target_os = "macos")]
mod dic {
    use std::ffi::{c_char, c_void, CStr};
    use std::fmt::Write;
    use std::sync::atomic::{AtomicU16, Ordering};
    use std::sync::OnceLock;

    const FRAMEWORK: &CStr = c"/Library/Apple/System/Library/PrivateFrameworks/DeviceInterfaceClient.framework/DeviceInterfaceClient";
    const TADFU_FRAMEWORK: &CStr =
        c"/Library/Apple/System/Library/PrivateFrameworks/DeviceInterface.framework/DeviceInterface";
    const TIMEOUT_MS: u64 = 2000;

    type Create = unsafe extern "C" fn(*mut c_void) -> *mut c_void;
    type List = unsafe extern "C" fn(*mut c_void, *mut u64, *mut usize) -> bool;
    type Transfer = unsafe extern "C" fn(
        *mut c_void,
        u64,
        *const u64,
        u32,
        *const c_void,
        usize,
        *mut c_void,
        *mut usize,
    ) -> bool;

    extern "C" {
        fn dispatch_queue_create(label: *const c_char, attr: *mut c_void) -> *mut c_void;
    }

    struct Client {
        handle: *mut c_void,
        list: List,
        transfer: Transfer,
    }
    // The framework's client is an XPC connection wrapper, safe across threads.
    unsafe impl Send for Client {}
    unsafe impl Sync for Client {}

    fn client() -> Result<&'static Client, String> {
        static CLIENT: OnceLock<Result<Client, String>> = OnceLock::new();
        CLIENT
            .get_or_init(|| unsafe {
                let h = libc::dlopen(FRAMEWORK.as_ptr(), libc::RTLD_NOW | libc::RTLD_LOCAL);
                if h.is_null() {
                    return Err("DeviceInterfaceClient.framework not found".into());
                }
                let sym = |name: &CStr| libc::dlsym(h, name.as_ptr());
                let create = sym(c"device_interface_client_server_xpc_client_create");
                let list = sym(c"device_interface_client_server_xpc_client_list_devices");
                let transfer = sym(c"device_interface_client_server_xpc_client_transfer_data");
                if create.is_null() || list.is_null() || transfer.is_null() {
                    return Err(
                        "DeviceInterfaceClient.framework is missing expected symbols".into(),
                    );
                }
                let create: Create = std::mem::transmute(create);
                let queue = dispatch_queue_create(c"restorekit.kis".as_ptr(), std::ptr::null_mut());
                let handle = create(queue);
                if handle.is_null() {
                    return Err("could not connect to deviceinterfaced".into());
                }
                Ok(Client {
                    handle,
                    list: std::mem::transmute::<*mut c_void, List>(list),
                    transfer: std::mem::transmute::<*mut c_void, Transfer>(transfer),
                })
            })
            .as_ref()
            .map_err(Clone::clone)
    }

    fn interfaces() -> Result<Vec<u64>, String> {
        let c = client()?;
        let mut ids = [0u64; 16];
        let mut count = ids.len();
        if !unsafe { (c.list)(c.handle, ids.as_mut_ptr(), &mut count) } {
            return Err("deviceinterfaced list_devices failed".into());
        }
        Ok(ids[..count.min(ids.len())].to_vec())
    }

    #[link(name = "IOKit", kind = "framework")]
    extern "C" {
        fn IORegistryEntryIDMatching(id: u64) -> *const c_void;
        fn IOServiceGetMatchingService(main_port: u32, matching: *const c_void) -> u32;
        fn IORegistryEntryGetParentEntry(entry: u32, plane: *const c_char, parent: *mut u32)
            -> i32;
        fn IORegistryEntryGetRegistryEntryID(entry: u32, id: *mut u64) -> i32;
        fn IOObjectRelease(object: u32) -> i32;
    }

    /// Registry entry id of the parent (IOService plane) of the entry `id`.
    fn parent_id(id: u64) -> Option<u64> {
        unsafe {
            let entry = IOServiceGetMatchingService(0, IORegistryEntryIDMatching(id));
            if entry == 0 {
                return None;
            }
            let mut parent = 0;
            let kr = IORegistryEntryGetParentEntry(entry, c"IOService".as_ptr(), &mut parent);
            IOObjectRelease(entry);
            if kr != 0 {
                return None;
            }
            let mut pid = 0;
            let kr = IORegistryEntryGetRegistryEntryID(parent, &mut pid);
            IOObjectRelease(parent);
            (kr == 0).then_some(pid)
        }
    }

    /// The daemon's interface id for the device with this registry entry id.
    /// The ids are registry entry ids of the device's `IOUSBHostInterface`
    /// (seen on a live Debug USB device), so match on the parent or the device itself.
    pub fn interface_for(registry_id: u64) -> Result<u64, String> {
        let ids = interfaces()?;
        if let Some(id) = ids
            .iter()
            .find(|&&id| id == registry_id || parent_id(id) == Some(registry_id))
        {
            return Ok(*id);
        }
        match ids.as_slice() {
            [] => Err("deviceinterfaced lists no KIS interfaces".into()),
            _ => Err(format!(
                "{} KIS interfaces and none match this device",
                ids.len()
            )),
        }
    }

    /// Send one KIS request (12-byte header, args, payload) and return the raw
    /// reply. The daemon writes `scalars[1..]` out as little-endian u32 words
    /// followed by the input bytes, so the header goes in as scalars.
    pub fn request(id: u64, req: &[u8], reply_cap: usize) -> Result<Vec<u8>, String> {
        let c = client()?;
        // Replies are matched by the first header word and the daemon uses
        // 0xFFxx itself; the patched libirecovery uses 1..0x8000. Start each
        // process somewhere else, so two restores probing one Mac don't both
        // send the same number.
        static SEQ: AtomicU16 = AtomicU16::new(0);
        let start = (std::process::id() as u16).wrapping_mul(0x9e37);
        let seq = 0x8000 + start.wrapping_add(SEQ.fetch_add(1, Ordering::Relaxed)) % 0x7f00;
        let mut req = req.to_vec();
        req[..2].copy_from_slice(&seq.to_le_bytes());

        let words = (3 + req[4] as usize).min(15).min(req.len() / 4);
        let mut scalars = vec![TIMEOUT_MS];
        scalars.extend(
            req[..words * 4]
                .as_chunks::<4>()
                .0
                .iter()
                .map(|w| u32::from_le_bytes(*w) as u64),
        );
        let payload = &req[words * 4..];
        let mut out = vec![0u8; reply_cap];
        let mut out_len = out.len();
        let ok = unsafe {
            (c.transfer)(
                c.handle,
                id,
                scalars.as_ptr(),
                scalars.len() as u32,
                if payload.is_empty() {
                    std::ptr::null()
                } else {
                    payload.as_ptr().cast()
                },
                payload.len(),
                out.as_mut_ptr().cast(),
                &mut out_len,
            )
        };
        if !ok {
            return Err("deviceinterfaced transfer_data failed".into());
        }
        out.truncate(out_len);
        Ok(out)
    }

    /// What the daemon reports: its KIS interfaces and TADFU devices.
    pub fn describe(out: &mut String) {
        match interfaces() {
            Ok(ids) => {
                let ids: Vec<String> = ids
                    .iter()
                    .map(|&i| match parent_id(i) {
                        Some(p) => format!("{i:#x} (on device {p:#x})"),
                        None => format!("{i:#x}"),
                    })
                    .collect();
                let _ = writeln!(out, "deviceinterfaced KIS interfaces: [{}]", ids.join(", "));
            }
            Err(e) => {
                let _ = writeln!(out, "deviceinterfaced: {e}");
            }
        }
        let _ = writeln!(out, "TADFU devices: {}", tadfu_devices());
    }

    /// `tadfu_transport_client_copy_all_devices_information`, described. This is
    /// the higher-level path Apple's MobileDevice uses for KIS restores; dumped
    /// so a hardware test shows what it offers if the raw path falls short.
    fn tadfu_devices() -> String {
        use core_foundation::base::{CFType, TCFType};
        type Cb = unsafe extern "C" fn(*const c_void, *mut c_void);
        type Create = unsafe extern "C" fn(Cb, *mut c_void, Cb, *mut c_void) -> *mut c_void;
        type Copy = unsafe extern "C" fn(*mut c_void) -> *const c_void;
        unsafe extern "C" fn ignore(_: *const c_void, _: *mut c_void) {}
        unsafe {
            let h = libc::dlopen(TADFU_FRAMEWORK.as_ptr(), libc::RTLD_NOW | libc::RTLD_LOCAL);
            if h.is_null() {
                return "DeviceInterface.framework not found".into();
            }
            let create = libc::dlsym(
                h,
                c"tadfu_transport_client_create_with_device_discovery_callbacks".as_ptr(),
            );
            let copy = libc::dlsym(
                h,
                c"tadfu_transport_client_copy_all_devices_information".as_ptr(),
            );
            if create.is_null() || copy.is_null() {
                return "DeviceInterface.framework is missing expected symbols".into();
            }
            let create: Create = std::mem::transmute(create);
            let copy: Copy = std::mem::transmute(copy);
            let client = create(ignore, std::ptr::null_mut(), ignore, std::ptr::null_mut());
            if client.is_null() {
                return "could not connect to the TADFU server".into();
            }
            // Discovery is asynchronous; give the initial device list a moment.
            std::thread::sleep(std::time::Duration::from_millis(500));
            let all = copy(client);
            if all.is_null() {
                return "none".into();
            }
            format!("{:?}", CFType::wrap_under_create_rule(all as _))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn apple_kis_reply(serial: &str) -> Vec<u8> {
        let mut reply = vec![0u8; APPLE_KIS_INFO_SIZE];
        reply[..4].copy_from_slice(&[0xac, 0x05, 0x27, 0x12]);
        reply[8..8 + 5].copy_from_slice(b"NONC:");
        reply[APPLE_KIS_SERIAL_OFFSET..APPLE_KIS_SERIAL_OFFSET + serial.len()]
            .copy_from_slice(serial.as_bytes());
        reply
    }

    #[test]
    fn reads_serial_from_apple_kis_reply() {
        let serial = "SDOM:01 CPID:8132 BDID:2A ECID:000A78D20A06401C SRTG:[iBoot-9082.0.0.300.1]";
        assert_eq!(
            classify_apple_kis(&apple_kis_reply(serial)),
            Read::Serial(serial.to_string())
        );
    }

    #[test]
    fn empty_apple_kis_serial_means_not_in_dfu() {
        assert_eq!(classify_apple_kis(&apple_kis_reply("")), Read::NotInDfu);
        assert_eq!(classify_apple_kis(&[0u8; 16]), Read::Failed);
    }

    #[test]
    fn header_matches_libirecovery() {
        // GET_INFO on the RSM portal, 0xC0 reply words, no args.
        assert_eq!(
            header(
                0,
                PORTAL_RSM,
                request_word(READ_REGISTERS, INDEX_GET_INFO, INFO_LEN / 4),
                0
            ),
            [0, 0, 0xa0, 0x10, 0, 0x00, 0x01, 0x03, 0, 0, 0, 0]
        );
        // Config write: one register, its value as the argument.
        assert_eq!(
            header(
                7,
                PORTAL_CONFIG,
                request_word(WRITE_REGISTERS, INDEX_ENABLE_A, 1),
                4
            ),
            [7, 0, 0xa0, 0x01, 1, 0x0a, 0x04, 0x00, 4, 0, 0, 0]
        );
    }

    #[test]
    fn parses_serial_from_info_block() {
        let serial = "CPID:8142 CPRV:01 BDID:0E ECID:001A2B3C4D5E6F70";
        let mut info = vec![0u8; INFO_LEN];
        let word = 0x40; // string at byte 0x100
        info[DESCRIPTOR_OFFSET + I_SERIAL_NUMBER] = word as u8;
        let off = word * 4;
        let utf16: Vec<u8> = serial.encode_utf16().flat_map(u16::to_le_bytes).collect();
        info[off] = (2 + utf16.len()) as u8;
        info[off + 1] = 3;
        info[off + 2..off + 2 + utf16.len()].copy_from_slice(&utf16);
        // Whatever follows the descriptor isn't part of the string.
        info[off + 2 + utf16.len()] = b'X';
        assert_eq!(serial_from_info(&info).as_deref(), Some(serial));
    }

    #[test]
    fn short_reply_means_not_in_dfu() {
        // What a booted iPhone with Debug USB on answered: no block at all.
        assert_eq!(parse_info(&[]), Read::NotInDfu);
        assert_eq!(parse_info(&[0u8; INFO_LEN]), Read::Failed);
    }

    #[test]
    fn rejects_non_string_descriptor() {
        let mut info = vec![0u8; INFO_LEN];
        info[DESCRIPTOR_OFFSET + I_SERIAL_NUMBER] = 0x40;
        info[0x100] = 4;
        info[0x101] = 1;
        assert!(serial_from_info(&info).is_none());
    }
}
