module

public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import CFSG.Certificates.Kernel.BabyMonster.Twin
public meta import CFSG.Certificates.Kernel.BabyMonster.TwinDy
public meta import CFSG.Certificates.Kernel.BabyMonster.TwinRank
public meta import CFSG.Certificates.Kernel.BabyMonster.TwinVec
public import CFSG.Certificates.Kernel.BabyMonster.TwinVec

namespace CFSG.KC.BM.Twin

open CFSG.KC.Eval

public meta def byteTabs (M : Array Nat) : Array (Array Nat) := Id.run do
  let mut T : Array (Array Nat) := #[]
  for c in [0:(M.size + 7) / 8] do
    let mut t : Array Nat := Array.replicate 256 0
    for m in [1:256] do
      let low := m &&& (256 - m)
      t := t.set! m (t[m ^^^ low]! ^^^ M[8 * c + low.log2]?.getD 0)
    T := T.push t
  return T

public meta def vecTabs (T : Array (Array Nat)) (v : Nat) : Nat := Id.run do
  let mut acc := 0
  let mut x := v
  let mut c := 0
  while x != 0 && c < T.size do
    let m := x % 256
    if m != 0 then acc := acc ^^^ T[c]![m]!
    x := x / 256
    c := c + 1
  return acc

public meta def forestSpin (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let (n, size, hash) ← header args
  let #[_, _, _, f, v0, v1, .nat k, x, y] := args | throw "forestSpin: arguments"
  let F ← nats "F" f
  unless F.size == n do throw s!"forestSpin: {F.size} codes"
  unless k < 64 do throw s!"forestSpin: row {k}"
  let roots := #[(stripRows n (← stripArg "V0" v0))[k]!, (stripRows n (← stripArg "V1" v1))[k]!]
  let X := byteTabs (← matRows "X" n x)
  let Y := byteTabs (← matRows "Y" n y)
  let mut S : Array Nat := Array.mkEmpty n
  for t in [0:n] do
    let c := F[t]!
    if 2 * n ≤ c then
      let some r := roots[c - 2 * n]? | throw s!"forestSpin: node {t} has root {c - 2 * n}"
      S := S.push r
    else
      unless c / 2 < t do throw s!"forestSpin: node {t} has parent {c / 2}"
      S := S.push (vecTabs (if c % 2 == 0 then X else Y) S[c / 2]!)
  outStrips n size hash (stripsOfRows n S)

public meta def vecStrip (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let (n, size, hash) ← header args
  let #[_, _, _, l, .nat o, .nat d] := args | throw "vecStrip: arguments"
  let L ← nats "L" l
  unless 0 < d do throw "vecStrip: stride 0"
  let mut R : Array Nat := #[]
  let mut i := o
  while i < L.size do
    unless L[i]! >>> n == 0 do throw s!"vecStrip: vector {i} past column {n}"
    R := R.push L[i]!
    i := i + d
  unless R.size ≤ 64 do throw s!"vecStrip: {R.size} rows"
  outStrip n size hash (rowsStrip n R)

public meta def blocks (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let #[l, .nat m] := args | throw "blocks: arguments"
  let L ← nats "L" l
  unless 0 < m do throw "blocks: blocks of size 0"
  let bs := (Array.range ((L.size + m - 1) / m)).map fun s =>
    Val.list ((L.extract (m * s) (m * s + m)).map .nat)
  return #[(.anonymous, .list bs)]

public meta def xorI (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let (n, size, hash) ← header args
  let some (Val.nat e) := args[3]? | throw "xorI: no coefficient"
  let mut acc : Array Nat := if e % 2 == 1 then stripsOfRows n ((Array.range n).map (1 <<< ·))
    else Array.replicate ((n + 63) / 64) 0
  for i in [4:args.size] do
    let A ← strips s!"A{i - 4}" n args[i]!
    acc := (Array.range acc.size).map fun s => acc[s]! ^^^ A[s]!
  outStrips n size hash acc

end CFSG.KC.BM.Twin
