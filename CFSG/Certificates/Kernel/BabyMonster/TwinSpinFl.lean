module

public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import CFSG.Certificates.Kernel.BabyMonster.Twin
public meta import CFSG.Certificates.Kernel.BabyMonster.TwinVec
public meta import CFSG.Certificates.Kernel.BabyMonster.TwinRank
public import CFSG.Certificates.Kernel.BabyMonster.TwinVec

namespace CFSG.KC.BM.Twin

open CFSG.KC.Eval

public meta def spinFl (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let (n, size, hash) ← header args
  let #[_, _, _, .nat v, x1, x2, .nat len, .nat fl] := args | throw "spin: arguments"
  unless v >>> n == 0 do throw s!"spin: vector past column {n}"
  let M1 ← matRows "X1" n x1
  let M2 ← matRows "X2" n x2
  let mut R : Array Nat := #[v]
  for t in [0:len] do
    if (fl >>> t) &&& 1 == 1 then
      let some r := R[t / 2]? | throw s!"spin: flag {t} before row {t / 2}"
      R := R.push (vecRows n (if t % 2 == 0 then M1 else M2) r)
  unless R.size == n do throw s!"spin: {R.size} rows"
  outStrips n size hash (stripsOfRows n R)

end CFSG.KC.BM.Twin
