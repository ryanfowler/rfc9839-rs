//! # RFC 9839 Unicode Subset Validators
//!
//! This crate provides fast, zero-allocation checks to validate whether
//! individual characters, strings, or raw byte slices conform to the subsets
//! defined in [RFC 9839]:
//!
//! - **Unicode Scalars** — all code points except the UTF-16 surrogate range.
//!   In Rust, all `char` values are scalars by construction, but functions are
//!   included for completeness and defensive validation of `&str` / byte data.
//! - **XML Characters** — the “Char” production from XML:
//!   `{TAB, LF, CR} ∪ [0x20–0xD7FF] ∪ [0xE000–0xFFFD] ∪ [0x10000–0x10FFFF]`.
//!   Excludes legacy controls and noncharacters such as U+FFFE/U+FFFF.
//! - **Unicode Assignables** — “not problematic” characters: useful controls,
//!   printable ASCII (excluding DEL/C1), and all assigned scalars minus the
//!   standardized noncharacters (…FFFE/FFFF in each plane and U+FDD0–FDEF).
//!
//! ## Features
//!
//! - **Character-level** APIs (`is_*_char`) implemented as `const fn` with
//!   simple range tests.
//! - **String-level** APIs (`is_*`) with an ASCII fast-path: scan raw bytes
//!   first, and only fall back to `chars()` after the first non-ASCII byte.
//! - **Byte-level** APIs (`is_*_bytes`) for validating raw UTF-8 input. The tail
//!   is decoded once, returning `false` on invalid UTF-8.
//! - Zero allocations, no heap lookups, no tables.
//!
//! ## Examples
//!
//! ```
//! use rfc9839::*;
//!
//! // Scalars (always true for safe Rust strings)
//! assert!(is_unicode_scalar("hello 🌍"));
//!
//! // XML Characters
//! assert!(is_xml_chars("ok\tline\n"));
//! assert!(!is_xml_chars("\u{0000}")); // NUL is disallowed
//!
//! // Unicode Assignables
//! assert!(is_unicode_assignable("emoji 👍"));
//! assert!(!is_unicode_assignable("\u{007F}")); // DEL is excluded
//! ```
//!
//! ## Performance
//!
//! All string/byte checks run in O(n). ASCII data is validated in a tight loop;
//! non-ASCII triggers a one-time `chars()` traversal or UTF-8 decode. These
//! functions are designed for high-throughput pipelines, parsers, and
//! validators.
//!
//! [RFC 9839]: https://www.rfc-editor.org/rfc/rfc9839

/// Returns `true` if `c` is a Unicode scalar value per RFC 9839.
///
/// Any code point except the UTF-16 surrogate range `U+D800..=U+DFFF`.
///
/// In Rust, every `char` is already a scalar value by construction, so this
/// function will return `true` for all valid `char`s. It’s provided for
/// completeness and symmetry with the string/byte variants.
///
/// # Examples
/// ```
/// use rfc9839::*;
///
/// assert!(is_unicode_scalar_char('a'));
/// assert!(is_unicode_scalar_char('👍'));
/// ```
#[inline(always)]
#[must_use]
pub const fn is_unicode_scalar_char(c: char) -> bool {
    let u = c as u32;
    u <= 0xD7FF || (u >= 0xE000 && u <= 0x10FFFF)
}

/// Returns `true` if `c` is an XML Character as defined in RFC 9839.
///
/// `{ TAB, LF, CR } ∪ [0x20–0xD7FF] ∪ [0xE000–0xFFFD] ∪ [0x10000–0x10FFFF]`.
///
/// This is the classic XML “Char” set (controls removed except TAB/LF/CR,
/// and excluding noncharacters U+FFFE/U+FFFF).
///
/// # Examples
/// ```
/// use rfc9839::*;
///
/// assert!(is_xml_char('\t'));
/// assert!(is_xml_char('A'));
/// assert!(!is_xml_char('\u{0001}')); // disallowed control
/// assert!(!is_xml_char('\u{FFFF}')); // noncharacter
/// ```
#[inline(always)]
#[must_use]
pub const fn is_xml_char(c: char) -> bool {
    let u = c as u32;
    (u == 0x09)
        || (u == 0x0A)
        || (u == 0x0D)
        || (u >= 0x20 && u <= 0xD7FF)
        || (u >= 0xE000 && u <= 0xFFFD)
        || (u >= 0x10000 && u <= 0x10FFFF)
}

/// Returns `true` if `c` is a Unicode Assignable character per RFC 9839.
///
/// “not problematic” characters - allowing TAB/LF/CR, printable ASCII (excluding
/// DEL/C1), and all assigned scalars minus the standardized noncharacters
/// (…FFFE/FFFF in each plane and U+FDD0..=U+FDEF).
///
/// # Examples
/// ```
/// use rfc9839::*;
///
/// assert!(is_unicode_assignable_char('A'));
/// assert!(is_unicode_assignable_char('👍'));
/// assert!(!is_unicode_assignable_char('\u{007F}'));   // DEL
/// assert!(!is_unicode_assignable_char('\u{0085}'));   // C1 control
/// assert!(!is_unicode_assignable_char('\u{FDD0}'));   // noncharacter
/// assert!(!is_unicode_assignable_char('\u{1FFFE}'));  // plane noncharacter
/// ```
#[inline(always)]
#[must_use]
pub const fn is_unicode_assignable_char(c: char) -> bool {
    let u = c as u32;
    (u == 0x09)
        || (u == 0x0A)
        || (u == 0x0D)
        || (u >= 0x20 && u <= 0x7E)
        || (u >= 0xA0 && u <= 0xD7FF)
        || (u >= 0xE000 && u <= 0xFDCF)
        || (u >= 0xFDF0 && u <= 0xFFFD)
        || (u >= 0x10000 && u <= 0x1FFFD)
        || (u >= 0x20000 && u <= 0x2FFFD)
        || (u >= 0x30000 && u <= 0x3FFFD)
        || (u >= 0x40000 && u <= 0x4FFFD)
        || (u >= 0x50000 && u <= 0x5FFFD)
        || (u >= 0x60000 && u <= 0x6FFFD)
        || (u >= 0x70000 && u <= 0x7FFFD)
        || (u >= 0x80000 && u <= 0x8FFFD)
        || (u >= 0x90000 && u <= 0x9FFFD)
        || (u >= 0xA0000 && u <= 0xAFFFD)
        || (u >= 0xB0000 && u <= 0xBFFFD)
        || (u >= 0xC0000 && u <= 0xCFFFD)
        || (u >= 0xD0000 && u <= 0xDFFFD)
        || (u >= 0xE0000 && u <= 0xEFFFD)
        || (u >= 0xF0000 && u <= 0xFFFFD)
        || (u >= 0x100000 && u <= 0x10FFFD)
}

/// Returns `true` if all code points in `s` are Unicode scalar values.
///
/// In safe Rust, any well-formed `&str` contains only scalar values, so this
/// check will return `true`. It still performs a fast ASCII scan and then
/// verifies the remainder via `chars()` for defensive validation.
///
/// # Examples
/// ```
/// use rfc9839::*;
///
/// assert!(is_unicode_scalar("hello 🌍"));
/// ```
#[inline]
#[must_use]
pub fn is_unicode_scalar(s: &str) -> bool {
    let bytes = s.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        let b = bytes[i];
        if b < 0x80 {
            i += 1;
        } else {
            // non-ASCII: validate the remainder with full char checks
            return s[i..].chars().all(is_unicode_scalar_char);
        }
    }
    true
}

/// Returns `true` if all characters in `s` are XML Characters.
///
/// Validates using an ASCII fast-path (TAB/LF/CR and 0x20..=0x7E), then
/// switches to `chars()` on the first non-ASCII byte.
///
/// # Examples
/// ```
/// use rfc9839::*;
///
/// assert!(is_xml_chars("ok\tline\n"));
/// assert!(!is_xml_chars("\u{0000}")); // NUL disallowed
/// assert!(!is_xml_chars("\u{FFFF}")); // noncharacter
/// ```
#[inline]
#[must_use]
pub fn is_xml_chars(s: &str) -> bool {
    let bytes = s.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        let b = bytes[i];
        if b < 0x80 {
            if !ascii_ok(b) {
                return false;
            }
            i += 1;
        } else {
            // non-ASCII: validate the remainder with full char checks
            return s[i..].chars().all(is_xml_char);
        }
    }
    true
}

/// Returns `true` if all characters in `s` are Unicode Assignables.
///
/// Allows TAB/LF/CR, printable ASCII (excluding DEL), and assigned scalars
/// minus standardized noncharacters across all planes.
///
/// # Examples
/// ```
/// use rfc9839::*;
///
/// assert!(is_unicode_assignable("Hello 👍"));
/// assert!(!is_unicode_assignable("\u{007F}"));  // DEL
/// assert!(!is_unicode_assignable("\u{1FFFE}")); // plane noncharacter
/// ```
#[inline]
#[must_use]
pub fn is_unicode_assignable(s: &str) -> bool {
    let bytes = s.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        let b = bytes[i];
        if b < 0x80 {
            if !ascii_ok(b) {
                return false;
            }
            i += 1;
        } else {
            // non-ASCII: validate the remainder with full char checks
            return s[i..].chars().all(is_unicode_assignable_char);
        }
    }
    true
}

/// Returns `true` if `bytes` are valid Unicode scalar values.
///
/// If a non-ASCII byte is encountered, the remainder is validated by decoding
/// as UTF-8; invalid UTF-8 returns `false`.
///
/// # Examples
/// ```
/// use rfc9839::*;
///
/// assert!(is_unicode_scalar_bytes(b"ASCII only"));
/// assert!(is_unicode_scalar_bytes("héllo".as_bytes()));
/// assert!(!is_unicode_scalar_bytes(&[0xF0, 0x28, 0x8C, 0x28])); // invalid UTF-8
/// ```
#[inline]
#[must_use]
pub fn is_unicode_scalar_bytes(bytes: &[u8]) -> bool {
    let mut i = 0;
    while i < bytes.len() {
        let b = bytes[i];
        if b < 0x80 {
            i += 1;
        } else {
            // non-ASCII: validate the remainder with full char checks
            return if let Ok(s) = std::str::from_utf8(&bytes[i..]) {
                s.chars().all(is_unicode_scalar_char)
            } else {
                false
            };
        }
    }
    true
}

/// Returns `true` if `bytes` are all valid XML Characters.
///
/// On the first non-ASCII byte, the tail is decoded as UTF-8; invalid UTF-8
/// returns `false`.
///
/// # Examples
/// ```
/// use rfc9839::*;
///
/// assert!(is_xml_chars_bytes(b"ok\t\n\r ASCII"));
/// assert!(!is_xml_chars_bytes(&[0x00])); // NUL not allowed
/// assert!(!is_xml_chars_bytes("a\u{FFFF}".as_bytes())); // noncharacter
/// ```
#[inline]
#[must_use]
pub fn is_xml_chars_bytes(bytes: &[u8]) -> bool {
    let mut i = 0;
    while i < bytes.len() {
        let b = bytes[i];
        if b < 0x80 {
            if !ascii_ok(b) {
                return false;
            }
            i += 1;
        } else {
            // non-ASCII: validate the remainder with full char checks
            return if let Ok(s) = std::str::from_utf8(&bytes[i..]) {
                s.chars().all(is_xml_char)
            } else {
                false
            };
        }
    }
    true
}

/// Returns `true` if `bytes` are all valid Unicode Assignables.
///
/// On the first non-ASCII byte, the tail is decoded as UTF-8; invalid UTF-8
/// returns `false`.
///
/// # Examples
/// ```
/// use rfc9839::*;
///
/// assert!(is_unicode_assignable_bytes(b"Hello World"));
/// assert!(is_unicode_assignable_bytes("👍".as_bytes()));
/// assert!(!is_unicode_assignable_bytes(&[0x7F])); // DEL not allowed
/// assert!(!is_unicode_assignable_bytes("x\u{1FFFE}".as_bytes())); // plane noncharacter
/// ```
#[inline]
#[must_use]
pub fn is_unicode_assignable_bytes(bytes: &[u8]) -> bool {
    let mut i = 0;
    while i < bytes.len() {
        let b = bytes[i];
        if b < 0x80 {
            if !ascii_ok(b) {
                return false;
            }
            i += 1;
        } else {
            // non-ASCII: validate the remainder with full char checks
            return if let Ok(s) = std::str::from_utf8(&bytes[i..]) {
                s.chars().all(is_unicode_assignable_char)
            } else {
                false
            };
        }
    }
    true
}

#[inline(always)]
fn ascii_ok(b: u8) -> bool {
    // {TAB, LF, CR} or 0x20..=0x7E
    b == b'\t' || b == b'\n' || b == b'\r' || (b >= 0x20 && b <= 0x7E)
}

#[cfg(test)]
mod tests {
    use super::*;

    // ---- Helpers ------------------------------------------------------------

    /// Generate a few representative scalar characters across ranges.
    fn sample_scalars() -> [char; 8] {
        [
            '\u{0000}', // NUL (scalar, though not XML/Assignable)
            'A',
            '\u{007E}',  // '~'
            '\u{00A0}',  // NBSP
            '\u{D7FF}',  // last before surrogates
            '\u{E000}',  // first after surrogates (PUA)
            '\u{FFFD}',  // replacement char
            '\u{1F600}', // 😀
        ]
    }

    fn make_ascii(n: usize) -> String {
        "A".repeat(n)
    }

    // Noncharacters FFFE/FFFF at base plane.
    const BMP_FFFE: char = '\u{FFFE}';
    const BMP_FFFF: char = '\u{FFFF}';

    // ---- is_unicode_scalar_char --------------------------------------------

    #[test]
    fn scalar_char_accepts_all_valid_char() {
        for c in sample_scalars() {
            assert!(is_unicode_scalar_char(c), "char U+{:04X}", c as u32);
        }
    }

    #[test]
    fn scalar_char_rejects_surrogates_by_construction() {
        // You cannot construct a Rust `char` in the surrogate range; this test
        // documents that invariant indirectly by checking boundary neighbors.
        assert!(is_unicode_scalar_char('\u{D7FF}'));
        assert!(is_unicode_scalar_char('\u{E000}'));
        // (No direct surrogate `char` value to test.)
    }

    // ---- is_xml_char --------------------------------------------------------

    #[test]
    fn xml_char_allows_tab_lf_cr_and_printables() {
        for &c in &['\t', '\n', '\r', ' ', 'A', '~'] {
            assert!(is_xml_char(c), "expected XML char: {:?}", c);
        }
    }

    #[test]
    fn xml_char_disallows_other_c0_controls_and_nonchars() {
        assert!(!is_xml_char('\u{0000}'));
        assert!(!is_xml_char('\u{001F}')); // Unit Separator (C0)
        assert!(!is_xml_char(BMP_FFFE));
        assert!(!is_xml_char(BMP_FFFF));
    }

    #[test]
    fn xml_char_allows_valid_planes() {
        assert!(is_xml_char('\u{D7FF}')); // boundary
        assert!(is_xml_char('\u{E000}')); // boundary (PUA)
        assert!(is_xml_char('\u{FFFD}')); // replacement char
        assert!(is_xml_char('\u{10000}')); // start of SMP
        assert!(is_xml_char('\u{10FFFF}')); // max scalar
    }

    // ---- is_unicode_assignable_char ----------------------------------------

    #[test]
    fn assignable_char_allows_useful_controls_and_printable_ascii() {
        for &c in &['\t', '\n', '\r', ' ', 'A', '~'] {
            assert!(
                is_unicode_assignable_char(c),
                "expected assignable: {:?}",
                c
            );
        }
    }

    #[test]
    fn assignable_char_rejects_del_and_c1_controls() {
        assert!(!is_unicode_assignable_char('\u{007F}')); // DEL
        for cp in 0x80u32..=0x9Fu32 {
            let c = char::from_u32(cp).unwrap();
            assert!(!is_unicode_assignable_char(c), "C1 control U+{:04X}", cp);
        }
    }

    #[test]
    fn assignable_char_rejects_standardized_noncharacters() {
        // FDD0..FDEF
        for cp in 0xFDD0u32..=0xFDEFu32 {
            let c = char::from_u32(cp).unwrap();
            assert!(
                !is_unicode_assignable_char(c),
                "U+{:04X} should be excluded",
                cp
            );
        }
        // ...FFFE and ...FFFF in several planes
        let planes = [0x00000u32, 0x10000, 0x20000, 0xE0000, 0xF0000, 0x100000];
        for base in planes {
            let fffe = char::from_u32(base + 0xFFFE).unwrap();
            let ffff = char::from_u32(base + 0xFFFF).unwrap();
            assert!(
                !is_unicode_assignable_char(fffe),
                "U+{:06X} excluded",
                base + 0xFFFE
            );
            assert!(
                !is_unicode_assignable_char(ffff),
                "U+{:06X} excluded",
                base + 0xFFFF
            );
        }
    }

    #[test]
    fn assignable_char_allows_up_to_fffd_each_plane() {
        // Spot-check multiple planes at ...FFFD
        let ok_points = [0x00FFFD, 0x01FFFD, 0x02FFFD, 0x0EFFFD, 0x0FFFFD, 0x10FFFD];
        for cp in ok_points {
            let c = char::from_u32(cp).unwrap();
            assert!(
                is_unicode_assignable_char(c),
                "U+{:06X} should be allowed",
                cp
            );
        }
    }

    // ---- String validators --------------------------------------------------

    #[test]
    fn unicode_scalar_str_is_true_for_valid_utf8() {
        assert!(is_unicode_scalar("hello"));
        assert!(is_unicode_scalar("héllo"));
        assert!(is_unicode_scalar("emoji 👍"));
        assert!(is_unicode_scalar(&make_ascii(1024)));
    }

    #[test]
    fn xml_chars_str_basic_cases() {
        assert!(is_xml_chars("ok\tline\n\rmore"));
        assert!(!is_xml_chars("\u{0000}"));
        assert!(!is_xml_chars(&format!("x{}", BMP_FFFE)));
        assert!(is_xml_chars("valid \u{FFFD} char"));
    }

    #[test]
    fn assignable_str_basic_cases() {
        assert!(is_unicode_assignable("Hello 👍"));
        assert!(!is_unicode_assignable("\u{007F}")); // DEL
        assert!(!is_unicode_assignable("\u{0085}")); // C1 control
        assert!(!is_unicode_assignable("\u{FDD0}")); // noncharacter
        assert!(!is_unicode_assignable("\u{1FFFE}")); // plane noncharacter
    }

    #[test]
    fn ascii_fast_path_large_strings() {
        let s = make_ascii(4096);
        assert!(is_xml_chars(&s));
        assert!(is_unicode_assignable(&s));
    }

    #[test]
    fn mixed_ascii_then_utf8_tail() {
        let s = format!("{}{}", make_ascii(64), "👍👍👍");
        assert!(is_xml_chars(&s));
        assert!(is_unicode_assignable(&s));
    }

    // ---- Byte-slice validators ---------------------------------------------

    #[test]
    fn unicode_scalar_bytes_valid_and_invalid_utf8() {
        assert!(is_unicode_scalar_bytes(b"ASCII only"));
        assert!(is_unicode_scalar_bytes("héllo".as_bytes()));

        // Invalid UTF-8: overlong / bad continuation (classic example)
        let invalid = [0xF0, 0x28, 0x8C, 0x28];
        assert!(!is_unicode_scalar_bytes(&invalid));
    }

    #[test]
    fn xml_chars_bytes_respects_ascii_rules_and_utf8_decode() {
        assert!(is_xml_chars_bytes(b"ok\t\n\r ASCII"));
        assert!(!is_xml_chars_bytes(&[0x00])); // NUL forbidden

        let with_nonchar = "x\u{FFFF}".as_bytes().to_vec();
        assert!(!is_xml_chars_bytes(&with_nonchar));

        let invalid_utf8 = [0xE2, 0x28, 0xA1]; // invalid 3-byte sequence
        assert!(!is_xml_chars_bytes(&invalid_utf8));
    }

    #[test]
    fn assignable_bytes_respects_exclusions() {
        assert!(is_unicode_assignable_bytes(b"Hello World"));
        assert!(is_unicode_assignable_bytes("👍".as_bytes()));
        assert!(!is_unicode_assignable_bytes(&[0x7F])); // DEL
        let with_plane_nonchar = "x\u{1FFFE}".as_bytes().to_vec();
        assert!(!is_unicode_assignable_bytes(&with_plane_nonchar));
    }

    // ---- Internal ASCII helper ---------------------------------------------

    #[test]
    fn ascii_ok_rules() {
        // Allowed: TAB/LF/CR and 0x20..=0x7E
        for &b in &[b'\t', b'\n', b'\r', b' ', b'~'] {
            assert!(super::ascii_ok(b), "byte 0x{:02X} should be ok", b);
        }
        // Disallowed: other C0 (e.g., 0x1F) and DEL (0x7F)
        assert!(!super::ascii_ok(0x1F));
        assert!(!super::ascii_ok(0x7F));
    }

    // ---- Boundary sweeps (targeted) ----------------------------------------

    #[test]
    fn xml_boundaries() {
        // Lower boundary around 0x20
        assert!(!is_xml_char('\u{001F}'));
        assert!(is_xml_char('\u{0020}'));

        // D7FF/E000 boundary
        assert!(is_xml_char('\u{D7FF}'));
        assert!(is_xml_char('\u{E000}'));

        // FFFD/FFFE/FFFF boundary
        assert!(is_xml_char('\u{FFFD}'));
        assert!(!is_xml_char('\u{FFFE}'));
        assert!(!is_xml_char('\u{FFFF}'));
    }

    #[test]
    fn assignable_boundaries() {
        // ASCII printable vs DEL
        assert!(is_unicode_assignable_char('\u{007E}'));
        assert!(!is_unicode_assignable_char('\u{007F}'));

        // A0 start allowed
        assert!(is_unicode_assignable_char('\u{00A0}'));
        // D7FF end allowed, E000 start allowed
        assert!(is_unicode_assignable_char('\u{D7FF}'));
        assert!(is_unicode_assignable_char('\u{E000}'));

        // FDCF allowed, FDD0..FDEF excluded, FDF0 allowed
        assert!(is_unicode_assignable_char('\u{FDCF}'));
        assert!(!is_unicode_assignable_char('\u{FDD0}'));
        assert!(!is_unicode_assignable_char('\u{FDEF}'));
        assert!(is_unicode_assignable_char('\u{FDF0}'));

        // FFfd allowed, FFFE/FFFF not
        assert!(is_unicode_assignable_char('\u{FFFD}'));
        assert!(!is_unicode_assignable_char('\u{FFFE}'));
        assert!(!is_unicode_assignable_char('\u{FFFF}'));
    }

    #[test]
    fn supplementary_plane_boundaries_assignable() {
        // At plane starts and ...FFFD ends
        for plane in 0x1u32..=0x10 {
            let start = (plane << 16) + 0x0000;
            let end_ok = (plane << 16) + 0xFFFD;
            let end_bad1 = (plane << 16) + 0xFFFE;
            let end_bad2 = (plane << 16) + 0xFFFF;

            // Skip surrogates (plane 0 has them in D800..DFFF), we are testing supplementary planes.
            let start_char = char::from_u32(start).unwrap();
            let ok_char = char::from_u32(end_ok).unwrap();
            let bad1_char = char::from_u32(end_bad1).unwrap();
            let bad2_char = char::from_u32(end_bad2).unwrap();

            assert!(
                is_unicode_assignable_char(start_char),
                "U+{:06X} should be allowed",
                start
            );
            assert!(
                is_unicode_assignable_char(ok_char),
                "U+{:06X} should be allowed",
                end_ok
            );
            assert!(
                !is_unicode_assignable_char(bad1_char),
                "U+{:06X} should be excluded",
                end_bad1
            );
            assert!(
                !is_unicode_assignable_char(bad2_char),
                "U+{:06X} should be excluded",
                end_bad2
            );
        }
    }

    // ---- Sanity: mixed strings including boundaries ------------------------

    #[test]
    fn xml_and_assignable_mixed_strings() {
        let xml_ok = format!("start\t\n\r mid {} end", '\u{FFFD}');
        assert!(is_xml_chars(&xml_ok));
        let xml_bad = format!("x{}", '\u{FFFF}');
        assert!(!is_xml_chars(&xml_bad));

        let asg_ok = format!("hello {} world {}", '\u{00A0}', '\u{1F600}');
        assert!(is_unicode_assignable(&asg_ok));
        let asg_bad = format!("bad{}", '\u{1FFFE}');
        assert!(!is_unicode_assignable(&asg_bad));
    }
}
