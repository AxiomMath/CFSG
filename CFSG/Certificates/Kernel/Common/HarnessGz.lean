module

public meta import Lean
public import CFSG.Certificates.Kernel.Common.Harness
meta import all CFSG.Certificates.Kernel.Common.Harness

open Lean Elab Command

namespace CFSG.KC.Gz

meta def bit (b : ByteArray) (p : Nat) : Nat :=
  ((b.get! (p >>> 3)).toNat >>> (p &&& 7)) &&& 1

meta def bits (b : ByteArray) (p n : Nat) : Nat := Id.run do
  let mut v := 0
  for k in [0:n] do
    v := v ||| (bit b (p + k) <<< k)
  return v

structure Huff where
  count : Array Nat
  sym : Array Nat

meta def Huff.ofLens (lens : Array Nat) : Huff := Id.run do
  let mut count := Array.replicate 16 0
  for l in lens do
    count := count.modify l (· + 1)
  let mut offs := Array.replicate 16 0
  for l in [1:15] do
    offs := offs.set! (l + 1) (offs[l]! + count[l]!)
  let mut sym := Array.replicate lens.size 0
  for s in [0:lens.size] do
    let l := lens[s]!
    if l != 0 then
      sym := sym.set! offs[l]! s
      offs := offs.modify l (· + 1)
  return { count, sym }

meta partial def Huff.decode (h : Huff) (b : ByteArray) (p : Nat) : Except String (Nat × Nat) :=
  go p 1 0 0 0
where
  go (p len code first index : Nat) : Except String (Nat × Nat) :=
    if len > 15 then .error "invalid Huffman code" else
    let code := code ||| bit b p
    let c := h.count[len]!
    if code < first + c then .ok (h.sym[index + (code - first)]!, p + 1)
    else go (p + 1) (len + 1) (code <<< 1) ((first + c) <<< 1) (index + c)

meta def lenBase : Array Nat :=
  #[3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115,
    131, 163, 195, 227, 258]
meta def lenExtra : Array Nat :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0]
meta def distBase : Array Nat :=
  #[1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537,
    2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577]
meta def distExtra : Array Nat :=
  #[0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12,
    13, 13]

meta def fixedLit (_ : Unit := ()) : Huff :=
  .ofLens ((Array.range 288).map fun s =>
    if s < 144 then 8 else if s < 256 then 9 else if s < 280 then 7 else 8)
meta def fixedDist (_ : Unit := ()) : Huff := .ofLens (Array.replicate 30 5)

meta def clOrder : Array Nat :=
  #[16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]

meta def dynCodes (b : ByteArray) (p : Nat) : Except String (Huff × Huff × Nat) := do
  let nlen := bits b p 5 + 257
  let ndist := bits b (p + 5) 5 + 1
  let ncode := bits b (p + 10) 4 + 4
  let mut p := p + 14
  let mut cl := Array.replicate 19 0
  for k in [0:ncode] do
    cl := cl.set! clOrder[k]! (bits b p 3)
    p := p + 3
  let hc := Huff.ofLens cl
  let mut lens : Array Nat := #[]
  while lens.size < nlen + ndist do
    let (s, p') ← hc.decode b p
    p := p'
    if s < 16 then lens := lens.push s
    else
      let (v, r, w) := if s == 16 then (lens.back?.getD 0, 3, 2)
        else if s == 17 then (0, 3, 3) else (0, 11, 7)
      if s == 16 && lens.isEmpty then throw "repeat with no previous length"
      let n := r + bits b p w
      p := p + w
      for _ in [0:n] do
        lens := lens.push v
  if lens.size != nlen + ndist then throw "code lengths overrun"
  return (.ofLens (lens.extract 0 nlen), .ofLens (lens.extract nlen (nlen + ndist)), p)

meta def inflate (b : ByteArray) (start : Nat) : Except String (ByteArray × Nat) := do
  let stop := 8 * b.size
  let mut p := 8 * start
  let mut out := ByteArray.empty
  let mut final := false
  while !final do
    if p + 3 > stop then throw "truncated stream"
    final := bits b p 1 == 1
    let ty := bits b (p + 1) 2
    p := p + 3
    if ty == 0 then
      let q := (p + 7) / 8
      if q + 4 > b.size then throw "truncated stored block"
      let len := b[q]!.toNat + 256 * b[q + 1]!.toNat
      if q + 4 + len > b.size then throw "truncated stored block"
      out := out ++ b.extract (q + 4) (q + 4 + len)
      p := 8 * (q + 4 + len)
    else if ty == 3 then throw "invalid block type"
    else
      let (lit, dist, p') ← if ty == 1 then pure (fixedLit, fixedDist, p) else dynCodes b p
      p := p'
      let mut done := false
      while !done do
        if p > stop then throw "truncated block"
        let (s, p') ← lit.decode b p
        p := p'
        if s < 256 then out := out.push s.toUInt8
        else if s == 256 then done := true
        else
          let i := s - 257
          if i ≥ 29 then throw "invalid length symbol"
          let len := lenBase[i]! + bits b p lenExtra[i]!
          p := p + lenExtra[i]!
          let (d, p') ← dist.decode b p
          p := p'
          if d ≥ 30 then throw "invalid distance symbol"
          let dst := distBase[d]! + bits b p distExtra[d]!
          p := p + distExtra[d]!
          if dst > out.size then throw "distance past the start"
          for _ in [0:len] do
            out := out.push out[out.size - dst]!
  if p > stop then throw "truncated stream"
  return (out, (p + 7) / 8)

meta partial def skipZ (b : ByteArray) (i : Nat) : Nat :=
  if i < b.size && b[i]! != 0 then skipZ b (i + 1) else i + 1

meta def gunzip (b : ByteArray) : Except String ByteArray := do
  if b.size < 18 || b[0]! != 0x1f || b[1]! != 0x8b || b[2]! != 8 then throw "not a gzip file"
  let flg := b[3]!.toNat
  let mut i := 10
  if flg &&& 4 != 0 then i := i + 2 + b[i]!.toNat + 256 * b[i + 1]!.toNat
  if flg &&& 8 != 0 then i := skipZ b i
  if flg &&& 16 != 0 then i := skipZ b i
  if flg &&& 2 != 0 then i := i + 2
  let (out, j) ← inflate b i
  if j + 8 != b.size then throw "trailing bytes after the gzip member"
  let isize := b[j + 4]!.toNat + (b[j + 5]!.toNat <<< 8) + (b[j + 6]!.toNat <<< 16) +
    (b[j + 7]!.toNat <<< 24)
  if isize != out.size % 2 ^ 32 then throw "length differs from the gzip trailer"
  return out

meta def readPinnedGz {m : Type → Type} [Monad m] [MonadOptions m] [MonadLiftT IO m] (rel : String)
    (size hash : Nat) : m ByteArray := do
  let path := (← CFSG.KC.Load.dataRoot) / rel
  monadLift (m := IO) do
  let z ← IO.FS.readBinFile path
  let b ← match gunzip z with
    | .ok b => pure b
    | .error e => throw (IO.userError s!"data file {path}: {e}")
  let h := b.hash.toNat
  unless b.size == size && h == hash do
    let msg := s!"data file {path}: decompressed size {b.size} hash {h}, pinned size {size} hash {hash}"
    throw (IO.userError msg)
  return b

end CFSG.KC.Gz

open CFSG.KC.Load CFSG.KC.Gz in
elab "#kc_decls_gz " pre:ident path:str size:num hash:num : command => do
  let b ← readPinnedGz path.getString size.getNat hash.getNat
  withSync <| loadLines pre.getId false b

open CFSG.KC.Load CFSG.KC.Gz in
elab "#kc_checks_gz " pre:ident path:str size:num hash:num : command => do
  let b ← readPinnedGz path.getString size.getNat hash.getNat
  withSync <| loadLines pre.getId true b
