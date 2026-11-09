module

public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import CFSG.Certificates.Kernel.BabyMonster.Twin
public meta import CFSG.Certificates.Kernel.BabyMonster.TwinDy
public meta import CFSG.Certificates.Kernel.BabyMonster.TwinRank
public import CFSG.Certificates.Kernel.BabyMonster.TwinRank

namespace CFSG.KC.BM.Twin

open CFSG.KC.Eval

public meta def transposeBlocks (nb A : Nat) : Nat := Id.run do
  let full : Nat := 18446744073709551615
  let blockRep := ((1 <<< (4096 * nb)) - 1) / ((1 <<< 4096) - 1)
  let wordRep := ((1 <<< (64 * 64 * nb)) - 1) / full
  let mut a := A
  let mut w : Nat := 32
  let mut m : Nat := 0x00000000FFFFFFFF
  while w > 0 do
    let mut p : Nat := 0
    for i in [0:64] do
      if i &&& w == 0 then p := p ||| (full <<< (64 * i))
    let sel := p * blockRep
    let mr := sel &&& (m * wordRep)
    let x := a &&& sel
    let y := (a >>> (64 * w)) &&& sel
    let t := ((x >>> w) ^^^ y) &&& mr
    a := (x ^^^ (t <<< w)) ||| ((y ^^^ t) <<< (64 * w))
    w := w / 2
    m := m ^^^ (m <<< w)
  return a

public meta def stripRows (n A : Nat) : Array Nat := Id.run do
  let nb := (n + 63) / 64
  let ws := natWords (transposeBlocks nb (A % (1 <<< (64 * n)))) (64 * nb)
  return (Array.range 64).map fun t =>
    natOfWords ((Array.range nb).map fun c => ws[64 * c + t]!) 0 nb

public meta def rowsStrip (n : Nat) (R : Array Nat) : Nat := Id.run do
  let nb := (n + 63) / 64
  let rw := (Array.range 64).map fun t =>
    if h : t < R.size then natWords R[t] nb else Array.replicate nb 0
  let ws := (Array.range (64 * nb)).map fun k => rw[k % 64]![k / 64]!
  return transposeBlocks nb (natOfWords ws 0 (64 * nb)) % (1 <<< (64 * n))

public meta def vecRows (n : Nat) (M : Array Nat) (v : Nat) : Nat := Id.run do
  if v == 0 then return 0
  let ws := natWords v ((n + 63) / 64)
  let mut acc := 0
  for c in [0:ws.size] do
    let mut w := ws[c]!
    while w != 0 do
      let low := w &&& (0 - w)
      acc := acc ^^^ M[64 * c + low.log2.toNat]?.getD 0
      w := w ^^^ low
  return acc

public meta def mulRows (n : Nat) (M : Array Nat) (A : Nat) : Nat :=
  rowsStrip n ((stripRows n A).map (vecRows n M))

public meta def spreadVec (n v : Nat) : Nat :=
  let ws := natWords v ((n + 63) / 64)
  natOfWords ((Array.range n).map fun j => (ws[j / 64]! >>> (j % 64).toUInt64) &&& 1) 0 n

public meta def stripArg (what : String) : Val → Except String Nat
  | .nat x => pure x
  | .list xs => match xs[0]? with
    | some (Val.nat x) => pure x
    | _ => throw s!"{what}: not a strip or a list of strips"
  | _ => throw s!"{what}: not a strip"

public meta def outStrip (n size hash A : Nat) : Except String (Array (Lean.Name × Val)) := do
  if size != 0 then
    let (bs, bh) := stripHash n #[A]
    unless bs == size && bh == hash do
      throw s!"result of size {bs} hash {bh}, pinned size {size} hash {hash}"
  return #[(.anonymous, .nat A)]

public meta def vword (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let (n, size, hash) ← header args
  let some a := args[3]? | throw "vword: no strip"
  let mut A ← stripArg "A" a
  for i in [4:args.size] do
    A := mulRows n (← matRows s!"M{i - 3}" n args[i]!) A
  outStrip n size hash A

public meta def vrepl (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let (n, size, hash) ← header args
  let (some s, some (Val.nat m0)) := (args[3]?, args[4]?) | throw "vrepl: expected S and m₀"
  unless args.size % 2 == 1 do throw "vrepl: a matrix without its mask"
  let S ← stripArg "S" s
  let sm := spreadMask n
  let mut ms : Array (Nat × Array Nat) := #[]
  let mut mAll := 0
  for k in [0:(args.size - 5) / 2] do
    let .nat m := args[6 + 2 * k]! | throw s!"vrepl: mask {k + 1} is not a number"
    ms := ms.push (m, ← matRows s!"M{k + 1}" n args[5 + 2 * k]!)
    mAll := mAll ||| m
  let V := stripRows n (S &&& (sm * mAll))
  let R := (Array.range 64).map fun t => Id.run do
    let mut r := 0
    for (m, M) in ms do
      if (m >>> t) &&& 1 == 1 then r := r ||| vecRows n M V[t]!
    return r
  outStrip n size hash ((S - (S &&& (sm * m0))) ||| rowsStrip n R)

public meta def vreplChain (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let (n, size, first) ← header args
  let (some s, some (Val.nat k)) := (args[3]?, args[4]?) | throw "vreplChain: expected S and k"
  let nb := (n + 63) / 64
  let mut Ts : Array (Array Nat) := #[]
  for i in [0:k] do
    let some mv := args[5 + i]? | throw s!"vreplChain: no matrix {i + 1}"
    Ts := Ts.push (twTable (← matRows s!"M{i + 1}" n mv) (8 * nb))
  let o := 5 + k
  let g := k + 2
  unless o ≤ args.size && (args.size - o) % g == 0 do
    throw "vreplChain: a step without all its numbers"
  let mut V := stripRows n (← stripArg "S" s)
  let mut outs : Array (Lean.Name × Val) := #[]
  for j in [0:(args.size - o) / g] do
    let mut xs : Array Nat := #[]
    for i in [0:g] do
      let .nat x := args[o + g * j + i]! | throw s!"vreplChain: step {j}: argument {i} not a number"
      xs := xs.push x
    let m0 := xs[1]!
    let W := V
    V := (Array.range 64).map fun t => Id.run do
      let mut r := if (m0 >>> t) &&& 1 == 1 then 0 else W[t]!
      if (Array.range k).any fun i => (xs[2 + i]! >>> t) &&& 1 == 1 then
        let ws := natWords W[t]! nb
        for i in [0:k] do
          if (xs[2 + i]! >>> t) &&& 1 == 1 then r := r ||| twRowMul Ts[i]! ws
      return r
    let A := rowsStrip n V
    discard <| outStrip n size xs[0]! A
    outs := outs.push (Lean.Name.mkSimple s!"S{first + j}", .nat A)
  return outs

public meta def vrow0 (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let (n, size, hash) ← header args
  let sm := spreadMask n
  let mut acc := 0
  for t in [0:args.size - 3] do
    acc := acc ||| ((← stripArg s!"X{t}" args[3 + t]!) &&& sm) <<< t
  outStrip n size hash acc

public meta def vbase (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let (n, size, hash) ← header args
  let #[_, _, _, .nat c, .nat m, v] := args | throw "vbase: arguments"
  let x ← match v with
    | .nat v => do
      unless v >>> n == 0 do throw s!"vbase: vector past column {n}"
      pure (spreadVec n v)
    | _ => do pure ((← stripArg "v" v) &&& spreadMask n)
  outStrip n size hash (c ||| x * m)

public meta def vorbit (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let (n, size, hash) ← header args
  let #[_, _, _, mv, .nat m] := args | throw "vorbit: arguments"
  unless 0 < m && m ≤ 64 do throw s!"vorbit: {m} rows"
  let M ← matRows "M" n mv
  let mut R : Array Nat := #[1]
  for _ in [1:m] do
    R := R.push (vecRows n M R.back!)
  outStrip n size hash (rowsStrip n R)

end CFSG.KC.BM.Twin
