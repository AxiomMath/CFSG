module

public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import CFSG.Certificates.Kernel.BabyMonster.Twin
public meta import CFSG.Certificates.Kernel.BabyMonster.TwinRank
public meta import CFSG.Certificates.Kernel.BabyMonster.TwinVec
public import CFSG.Certificates.Kernel.BabyMonster.TwinVec

namespace CFSG.KC.BM.Twin

open CFSG.KC.Eval

public meta def textLines (T : Nat) : Array (Array Nat) := Id.run do
  let nb := (T.log2 + 64) / 64
  let ws := natWords T nb
  let mut lines : Array (Array Nat) := #[]
  let mut cur : Array Nat := #[]
  let mut num : Nat := 0
  let mut inNum := false
  for i in [0:8 * nb] do
    let c := ((ws[i / 8]! >>> (8 * (i % 8)).toUInt64) &&& 255).toNat
    if 48 ≤ c && c ≤ 57 then
      num := 10 * num + (c - 48)
      inNum := true
    else
      if inNum then
        cur := cur.push num
        num := 0
        inNum := false
      if c == 10 then
        lines := lines.push cur
        cur := #[]
  if inNum then
    cur := cur.push num
  if cur.size > 0 then
    lines := lines.push cur
  return lines

public meta def rowText (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let (n, size, hash) ← header args
  let some (Val.nat t) := args[3]? | throw "rowText: no text"
  let some l := (textLines t)[0]? | throw "rowText: empty text"
  let mut v := 0
  for w in [0:l.size] do
    unless l[w]! < 2 ^ 56 do throw s!"rowText: chunk {w} past 56 bits"
    v := v ||| (l[w]! <<< (56 * w))
  unless v >>> n == 0 do throw s!"rowText: row past column {n}"
  if size != 0 then
    let mut b : ByteArray := ByteArray.emptyWithCapacity (8 * ((n + 63) / 64))
    for x in natWords v ((n + 63) / 64) do
      for i in [0:8] do
        b := b.push (x >>> (8 * i).toUInt64).toUInt8
    unless b.size == size && b.hash.toNat == hash do
      throw s!"result of size {b.size} hash {b.hash.toNat}, pinned size {size} hash {hash}"
  return #[(.anonymous, .nat v)]

public meta def spinRows (n : Nat) (tr : Array (Nat × Bool)) (v : Nat) (X Y : Array Nat) :
    Except String (Array Nat) := do
  let mut S : Array Nat := #[v]
  for (p, g) in tr do
    let some r := S[p]? | throw s!"spin: vector {p} is not spun yet"
    S := S.push (vecRows n (if g then Y else X) r)
  return S

public meta def intertw (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let (n, size, hash) ← header args
  unless 10 ≤ args.size do throw "intertw: arguments"
  let (Val.nat t, Val.nat v, Val.nat w) := (args[3]!, args[4]!, args[7]!)
    | throw "intertw: the tree and the rows v, w are numbers"
  let mut tr : Array (Nat × Bool) := #[]
  for l in (textLines t).filter (0 < ·.size) do
    let #[p, g] := l | throw "intertw: a tree line is not `p g`"
    unless g ≤ 1 do throw s!"intertw: generator {g}"
    tr := tr.push (p, g == 1)
  unless tr.size + 1 == n do throw s!"intertw: a tree of {tr.size} lines"
  let S ← spinRows n tr v (← matRows "X" n args[5]!) (← matRows "Y" n args[6]!)
  let S' ← spinRows n tr w (← matRows "X'" n args[8]!) (← matRows "Y'" n args[9]!)
  let some Si := invRows n S | throw "intertw: S is singular"
  let mut G := mulStrips n (stripsOfRows n Si) (stripsOfRows n S')
  for i in [10:args.size] do
    G := mulStrips n G (← matStrips s!"M{i - 9}" n args[i]!)
  outStrips n size hash G

end CFSG.KC.BM.Twin
