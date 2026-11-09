module

public meta import CFSG.Certificates.Kernel.Common.Eval
public import CFSG.Certificates.Kernel.Common.Eval

namespace CFSG.KC.BM.Twin

open CFSG.KC.Eval

public meta partial def natWords (x nw : Nat) : Array UInt64 :=
  if nw ≤ 1 then #[x.toUInt64]
  else if nw ≤ 4 then
    #[x.toUInt64, (x >>> 64).toUInt64, (x >>> 128).toUInt64, (x >>> 192).toUInt64].extract 0 nw
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

public meta def twRepunit (L cnt : Nat) : Nat := ((1 <<< (L * cnt)) - 1) / ((1 <<< L) - 1)

public meta def twSwapMask (K a b : Nat) : Nat :=
  let ha := 1 <<< a
  let hb := 1 <<< b
  (((1 <<< ha) - 1) <<< ha) * twRepunit (2 * ha) (hb / (2 * ha)) *
    twRepunit (2 * hb) ((1 <<< K) / (2 * hb))

public meta def stripSwaps : Array (Nat × Nat) := Id.run do
  let tgt := Array.range' 6 13 ++ Array.range 6
  let mut cur := Array.range 19
  let mut out := #[]
  for p in [0:19] do
    let q := (cur.findIdx? (· == tgt[p]!)).getD p
    if q != p then
      out := out.push ((1 <<< q) - (1 <<< p), twSwapMask 19 p q)
      cur := cur.swapIfInBounds p q
  return out

public meta def twPermBits (sw : Array (Nat × Nat)) (x : Nat) : Nat :=
  sw.foldl (fun x (d, M) => let t := (x ^^^ (x >>> d)) &&& M; x ^^^ t ^^^ (t <<< d)) x

public meta partial def natChunks (x L cnt : Nat) : Array Nat :=
  if cnt ≤ 1 then #[x]
  else
    let h := cnt / 2
    natChunks (x &&& ((1 <<< (L * h)) - 1)) L h ++ natChunks (x >>> (L * h)) L (cnt - h)

public meta partial def natJoin (xs : Array Nat) (L lo hi : Nat) : Nat :=
  if hi ≤ lo + 1 then (if lo < hi then xs[lo]! else 0)
  else
    let mid := (lo + hi) / 2
    natJoin xs L lo mid ||| (natJoin xs L mid hi <<< (L * (mid - lo)))

public meta def strip64Rows (sw : Array (Nat × Nat)) (n s x : Nat) : Array Nat :=
  (natChunks (twPermBits sw x) 8192 64).extract 0 (min 64 (n - 64 * s))

public meta def rowsOfStrips (n : Nat) (S : Array Nat) : Array Nat := Id.run do
  let sw := stripSwaps
  let mut rows : Array Nat := Array.mkEmpty n
  for s in [0:S.size] do
    rows := rows ++ strip64Rows sw n s S[s]!
  return rows

public meta def stripsOfRows (n : Nat) (R : Array Nat) : Array Nat :=
  let sw := stripSwaps.reverse
  (Array.range ((n + 63) / 64)).map fun s => twPermBits sw (natJoin R 8192 (64 * s) (min n (64 * s + 64)))

public meta def spreadMask (n : Nat) : Nat := ((1 <<< (64 * n)) - 1) / 18446744073709551615

public meta def twTable (R : Array Nat) (ng : Nat) : Array Nat := Id.run do
  let mut T : Array Nat := Array.mkEmpty (256 * ng)
  for g in [0:ng] do
    let mut blk : Array Nat := #[0]
    for i in [0:8] do
      let r := R[8 * g + i]?.getD 0
      blk := blk ++ blk.map (· ^^^ r)
    T := T ++ blk
  return T

public meta def twRowMul (T : Array Nat) (ws : Array UInt64) : Nat := Id.run do
  let mut acc := 0
  for c in [0:ws.size] do
    let w := ws[c]!
    let b := 2048 * c
    acc := acc ^^^ T[b + (w &&& 255).toNat]! ^^^ T[b + 256 + ((w >>> 8) &&& 255).toNat]!
      ^^^ T[b + 512 + ((w >>> 16) &&& 255).toNat]! ^^^ T[b + 768 + ((w >>> 24) &&& 255).toNat]!
      ^^^ T[b + 1024 + ((w >>> 32) &&& 255).toNat]! ^^^ T[b + 1280 + ((w >>> 40) &&& 255).toNat]!
      ^^^ T[b + 1536 + ((w >>> 48) &&& 255).toNat]! ^^^ T[b + 1792 + (w >>> 56).toNat]!
  return acc

public meta def mulStrips (n : Nat) (A B : Array Nat) : Array Nat := Id.run do
  let nb := (n + 63) / 64
  let sw := stripSwaps
  let T := twTable (rowsOfStrips n B) (8 * nb)
  let mut C : Array Nat := Array.mkEmpty A.size
  for s in [0:A.size] do
    let out := (strip64Rows sw n s A[s]!).map fun r => twRowMul T (natWords r nb)
    C := C.push (twPermBits sw.reverse (natJoin out 8192 0 out.size))
  return C

public meta def invRows (n : Nat) (R : Array Nat) : Option (Array Nat) := Id.run do
  let mut Z : Array Nat := (Array.range n).map fun i => R[i]! ||| (1 <<< (n + i))
  let mut c0 := 0
  while c0 < n do
    let k := min 8 (n - c0)
    for j in [0:k] do
      let c := c0 + j
      let mut p := c
      let mut found := false
      while !found && p < n do
        let mut r := Z[p]!
        for j' in [0:j] do
          if (r >>> (c0 + j')) &&& 1 == 1 then r := r ^^^ Z[c0 + j']!
        if (r >>> c) &&& 1 == 1 then
          found := true
          Z := (Z.set! p Z[c]!).set! c r
        else
          Z := Z.set! p r
          p := p + 1
      if !found then return none
      let zc := Z[c]!
      for j' in [0:j] do
        if (Z[c0 + j']! >>> c) &&& 1 == 1 then
          Z := Z.set! (c0 + j') (Z[c0 + j']! ^^^ zc)
    let mut T : Array Nat := #[0]
    for j in [0:k] do
      let r := Z[c0 + j]!
      T := T ++ T.map (· ^^^ r)
    let hm := (1 <<< (c0 + k)) - 1
    for i in [0:n] do
      if i < c0 || c0 + k ≤ i then
        let m := (Z[i]! &&& hm) >>> c0
        if m != 0 then
          Z := Z.set! i (Z[i]! ^^^ T[m]!)
    c0 := c0 + k
  return some (Z.map (· >>> n))

public meta def stripBytes (n : Nat) (S : Array Nat) : ByteArray := Id.run do
  let mut b : ByteArray := ByteArray.emptyWithCapacity (S.size * 8 * n)
  for x in S do
    for w in natWords x n do
      for i in [0:8] do
        b := b.push (w >>> (8 * i).toUInt64).toUInt8
  return b

public meta def stripHash (n : Nat) (S : Array Nat) : Nat × Nat := Id.run do
  let m : UInt64 := 0xc6a4a7935bd1e995
  let len := 8 * n * S.size
  let mut h : UInt64 := 11 ^^^ (len.toUInt64 * m)
  for x in S do
    for k0 in natWords x n do
      let k := k0 * m
      h := (h ^^^ ((k ^^^ (k >>> 47)) * m)) * m
  h := h ^^^ (h >>> 47)
  h := h * m
  h := h ^^^ (h >>> 47)
  return (len, h.toNat)

public meta def strips (what : String) (n : Nat) (v : Val) : Except String (Array Nat) := do
  let .list xs := v | throw s!"{what}: not a list"
  unless xs.size == (n + 63) / 64 do throw s!"{what}: {xs.size} strips"
  xs.mapM fun
    | .nat x => pure x
    | _ => throw s!"{what}: a strip is not a number"

public meta def outStrips (n size hash : Nat) (S : Array Nat) : Except String (Array (Lean.Name × Val)) := do
  if size != 0 then
    let (bs, bh) := stripHash n S
    unless bs == size && bh == hash do
      throw s!"result of size {bs} hash {bh}, pinned size {size} hash {hash}"
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
