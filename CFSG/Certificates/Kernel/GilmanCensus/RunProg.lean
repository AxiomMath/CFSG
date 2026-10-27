module

import all Certificates.Data.Census
public import Certificates.Data.Census

public section

namespace Certificates.GilmanCensusK

open Certificates.Census Std

abbrev C4 := Array Nat × Nat × Bool × Bool

@[expose] def dlInner (dt : Data) (x y : Array Nat) (a b : Nat) (dl : Array (Array Nat)) :
    CM (ForInStep (Array (Array Nat))) :=
  if (a != 0 || b != 0) = true then
    let z := line3 (Array.ofFn (n := dt.d) fun i => (a * x[i.val]! + b * y[i.val]!) % 3)
    if (!dl.contains z) = true then pure (ForInStep.yield (dl.push z))
    else pure (ForInStep.yield dl)
  else pure (ForInStep.yield dl)

@[expose] def dlOuter (dt : Data) (x y : Array Nat) (a : Nat) (dl : Array (Array Nat)) :
    CM (ForInStep (Array (Array Nat))) := do
  let r ← forIn [:3] dl (dlInner dt x y a)
  pure (ForInStep.yield r)

@[expose] def aVec (d : Nat) (dual : Array (Array Nat)) (code : Nat) : Array Nat :=
  Array.ofFn (n := d) fun i => Id.run do
    let mut s := 0
    let mut c := code
    for j in [0:dual.size] do
      s := s + (c % 3) * dual[j]![i.val]!
      c := c / 3
    return s % 3

@[expose] def availBody (dt : Data) (a : Array Nat) (cands : Array C4) (j : Nat) (avail : Array Nat) :
    CM (ForInStep (Array Nat)) := do
  let kj ← kernelM dt cands[j]!.2.1
  if (kj.size == 1 || kj.any fun k => dot3 a k != 0) = true then
    if (kj.size != 1) = true then do
      markBad
      pure (ForInStep.yield (avail.push j))
    else pure (ForInStep.yield (avail.push j))
  else pure (ForInStep.yield avail)

@[expose] def patBody (dt : Data) (cands : Array C4) (dual : Array (Array Nat)) (code : Nat)
    (patterns : Array (Array Nat)) : CM (ForInStep (Array (Array Nat))) :=
  let a := aVec dt.d dual code
  let nz := a.any (· != 0)
  if dt.d - (if nz then 1 else 0) < 4 then pure (ForInStep.yield patterns)
  else if (nz && line3 a != a) = true then pure (ForInStep.yield patterns)
  else do
    let avail ← forIn [:cands.size] (#[] : Array Nat) (availBody dt a cands)
    if (!patterns.contains avail) = true then pure (ForInStep.yield (patterns.push avail))
    else pure (ForInStep.yield patterns)

end Certificates.GilmanCensusK

end
