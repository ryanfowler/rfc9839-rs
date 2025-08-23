# rfc9839

[![Crates.io](https://img.shields.io/crates/v/rfc9839.svg)](https://crates.io/crates/rfc9839)
[![Docs.rs](https://docs.rs/rfc9839/badge.svg)](https://docs.rs/rfc9839)
[![License](https://img.shields.io/crates/l/rfc9839.svg)](#license)

Validation of [RFC 9839](https://www.rfc-editor.org/rfc/rfc9839) Unicode subsets in Rust.

RFC 9839 defines three nested subsets of Unicode characters for use in text protocols:

- **Unicode Scalars** – all code points except UTF-16 surrogates.
  *Every Rust `char` is already a scalar value; checks are included for completeness and for raw byte validation.*
- **XML Characters** – `{ TAB, LF, CR } ∪ [0x20–0xD7FF] ∪ [0xE000–0xFFFD] ∪ [0x10000–0x10FFFF]`.
  *This is the XML “Char” production with legacy controls and noncharacters excluded.*
- **Unicode Assignables** – “not problematic” characters: useful controls, printable ASCII (excluding DEL/C1),
  and all assigned scalars minus standardized noncharacters (…FFFE/FFFF in each plane and U+FDD0–FDEF).

---

## Features

- **Character-level APIs**: `is_unicode_scalar_char`, `is_xml_char`, `is_unicode_assignable_char`
- **String-level APIs**: `is_unicode_scalar`, `is_xml_chars`, `is_unicode_assignable`
- **Byte-level APIs**: `is_unicode_scalar_bytes`, `is_xml_chars_bytes`, `is_unicode_assignable_bytes`
- **ASCII fast-path**: tight loops for ASCII data, falling back to `chars()` only after the first non-ASCII byte
- **Zero allocations**, no lookup tables

## Example

```rust
use rfc9839::*;

// Scalars (always true for safe Rust strings)
assert!(is_unicode_scalar("hello 🌍"));

// XML Characters
assert!(is_xml_chars("ok\tline\n"));
assert!(!is_xml_chars("\u{0000}")); // NUL is disallowed

// Unicode Assignables
assert!(is_unicode_assignable("emoji 👍"));
assert!(!is_unicode_assignable("\u{007F}")); // DEL is excluded
```
