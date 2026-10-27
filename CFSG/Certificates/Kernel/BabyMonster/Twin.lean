module

public meta import CFSG.Certificates.Kernel.Common.Eval
public import CFSG.Certificates.Kernel.Common.Eval

namespace CFSG.KC.BM.Twin

open CFSG.KC.Eval

public meta partial def natWords (x nw : Nat) : Array UInt64 :=
  if nw ≤ 1 then #[x.toUInt64]
  else
    let h := nw / 2
    natWords (x % (1 <<< (64 * h))) h ++ natWords (x >>> (64 * h)) (nw - h)

public meta partial def natOfWords (ws : Array UInt64) (lo hi : Nat) : Nat :=
  if hi ≤ lo + 1 then (if lo < hi then ws[lo]!.toNat else 0)
  else
    let mid := (lo + hi) / 2
    natOfWords ws lo mid ||| (natOfWords ws mid hi <<< (64 * (mid - lo)))

public meta def transpose64 (a : Array UInt64) : Array UInt64 := Id.run do
  let mut a := a
  let mut w : Nat := 32
  let mut m : UInt64 := 0x00000000FFFFFFFF
  while w > 0 do
    for i in [0:64] do
      if i &&& w == 0 then
        let x := a[i]!
        let y := a[i + w]!
        let t := ((x >>> w.toUInt64) ^^^ y) &&& m
        a := a.set! (i + w) (y ^^^ t)
        a := a.set! i (x ^^^ (t <<< w.toUInt64))
    w := w / 2
    m := m ^^^ (m <<< w.toUInt64)
  return a

public meta def rowsOfStrips (n : Nat) (S : Array Nat) : Array Nat := Id.run do
  let nb := (n + 63) / 64
  let mut rows : Array Nat := Array.mkEmpty n
  for s in [0:nb] do
    let ws := natWords S[s]! n
    let mut rw : Array (Array UInt64) := Array.replicate 64 (Array.replicate nb 0)
    for c in [0:nb] do
      let blk := (Array.range 64).map fun j => if 64 * c + j < n then ws[64 * c + j]! else 0
      let tb := transpose64 blk
      for t in [0:64] do
        rw := rw.modify t (·.set! c tb[t]!)
    for t in [0:min 64 (n - 64 * s)] do
      rows := rows.push (natOfWords rw[t]! 0 nb)
  return rows

public meta def stripsOfRows (n : Nat) (R : Array Nat) : Array Nat := Id.run do
  let nb := (n + 63) / 64
  let mut S : Array Nat := Array.mkEmpty nb
  for s in [0:nb] do
    let rw := (Array.range 64).map fun t =>
      if 64 * s + t < n then natWords R[64 * s + t]! nb else Array.replicate nb 0
    let mut ws : Array UInt64 := Array.replicate (64 * nb) 0
    for c in [0:nb] do
      let tb := transpose64 ((Array.range 64).map fun t => rw[t]![c]!)
      for j in [0:64] do
        ws := ws.set! (64 * c + j) tb[j]!
    S := S.push (natOfWords ws 0 n)
  return S

public meta def spreadMask (n : Nat) : Nat := ((1 <<< (64 * n)) - 1) / 18446744073709551615

public meta def mulStrips (n : Nat) (A B : Array Nat) : Array Nat := Id.run do
  let S := spreadMask n
  let ws := A.map (natWords · n)
  let mut C : Array Nat := Array.replicate A.size 0
  for k in [0:n] do
    let sp := (B[k / 64]! >>> (k % 64)) &&& S
    for s in [0:A.size] do
      let w := ws[s]![k]!
      if w != 0 then C := C.modify s (· ^^^ (w.toNat * sp))
  return C

public meta def invRows (n : Nat) (R : Array Nat) : Option (Array Nat) := Id.run do
  let mut Z : Array Nat := (Array.range n).map fun i => R[i]! ||| (1 <<< (n + i))
  for c in [0:n] do
    let mut p := c
    while p < n && (Z[p]! >>> c) &&& 1 == 0 do
      p := p + 1
    if p == n then return none
    let zp := Z[p]!
    Z := (Z.set! p Z[c]!).set! c zp
    for i in [0:n] do
      if i != c && (Z[i]! >>> c) &&& 1 == 1 then
        Z := Z.set! i (Z[i]! ^^^ zp)
  return some (Z.map (· >>> n))

public meta def stripBytes (n : Nat) (S : Array Nat) : ByteArray := Id.run do
  let mut b : ByteArray := ByteArray.emptyWithCapacity (S.size * 8 * n)
  for x in S do
    for w in natWords x n do
      for i in [0:8] do
        b := b.push (w >>> (8 * i).toUInt64).toUInt8
  return b

public meta def strips (what : String) (n : Nat) (v : Val) : Except String (Array Nat) := do
  let .list xs := v | throw s!"{what}: not a list"
  unless xs.size == (n + 63) / 64 do throw s!"{what}: {xs.size} strips"
  xs.mapM fun
    | .nat x => pure x
    | _ => throw s!"{what}: a strip is not a number"

public meta def outStrips (n size hash : Nat) (S : Array Nat) : Except String (Array (Lean.Name × Val)) := do
  if size != 0 then
    let b := stripBytes n S
    unless b.size == size && b.hash.toNat == hash do
      throw s!"result of size {b.size} hash {b.hash.toNat}, pinned size {size} hash {hash}"
  let names := (Array.range S.size).map fun j => Lean.Name.mkSimple s!"s{j}"
  return (names.zip (S.map .nat)) |>.push (.anonymous, .list (names.map .ref))

public meta def header (args : Array Val) : Except String (Nat × Nat × Nat) :=
  match args[0]?, args[1]?, args[2]? with
  | some (Val.nat n), some (Val.nat size), some (Val.nat hash) =>
    if 4352 < n && n ≤ 4416 then .ok (n, size, hash) else .error s!"dimension {n}"
  | _, _, _ => .error "expected the dimension and the pin"

public meta def prod (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let (n, size, hash) ← header args
  let some a := args[3]? | throw "no matrix"
  let mut C ← strips "A" n a
  for i in [4:args.size] do
    C := mulStrips n C (← strips s!"B{i - 3}" n args[i]!)
  outStrips n size hash C

public meta def inv (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let (n, size, hash) ← header args
  let some y := args[3]? | throw "no matrix"
  let some R := invRows n (rowsOfStrips n (← strips "Y" n y)) | throw "singular matrix"
  outStrips n size hash (stripsOfRows n R)

end CFSG.KC.BM.Twin
