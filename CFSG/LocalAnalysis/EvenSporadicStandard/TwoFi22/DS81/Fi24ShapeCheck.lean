module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi24TwoBK
public import CFSG.LieType.Multipliers.U43Data

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open CFSG.Sporadic.FischerOddCore CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime

@[expose] def fi24ShapeZ : List ℤ :=
  [2, 1, -2, -2, -1, 2, 2, 1, 2, 2, 1, -2, 1, 1, 2, 2, 1, 1]

@[expose] def fi24ShapeX : List ℤ := [2, 1, 2, 1, 2, -1, -1, -2, -1, -1, 2, -1, -2, -1]

@[expose] def fi24ShapeY : List ℤ := [-2, -1, -1, 2, 1, 1, 2, -1, -1, 2]

@[expose] def fi24PLetterA (z : ℤ) : Array ℕ :=
  if z = 1 then fi24PStrong[0]! else if z = -1 then invCand 378 fi24PStrong[0]!
  else if z = 2 then fi24PStrong[1]! else invCand 378 fi24PStrong[1]!

@[expose] def fi24PWordA (w : List ℤ) : Array ℕ :=
  w.foldr (fun z t => compA 378 (fi24PLetterA z) t) (idA 378)

@[expose] def fi24RelA (X Xi Y Yi : Array ℕ) (v : List (Fin 2 × Bool)) : Array ℕ :=
  v.foldr (fun l t => compA 378 (if l.1.val = 0 then (if l.2 then X else Xi)
    else (if l.2 then Y else Yi)) t) (idA 378)

@[expose] def fi24SiftW (w : List ℤ) : Bool :=
  siftA 504 fi24KdLevels fi24KdBase.toArray 0 (fi24KWordA w)

@[expose] def fi24ShapeP : Bool :=
  let I := idA 378
  let Z := fi24PWordA fi24ShapeZ
  let Z2 := compA 378 Z Z
  let X := fi24PWordA fi24ShapeX
  let Y := fi24PWordA fi24ShapeY
  let Xi := invCand 378 X
  let Yi := invCand 378 Y
  let B := fi24PStrong[1]!
  isInvA 378 X Xi && isInvA 378 Y Yi &&
    eqA 378 (compA 378 Z Z2) I && !eqA 378 Z I &&
    fi24KdGenWords.all (fun w => let G := fi24PWordA w; eqA 378 (compA 378 G Z) (compA 378 Z G)) &&
    eqA 378 (compA 378 B Z) (compA 378 Z2 B) &&
    CFSG.LieType.Multipliers.U43.rels.all (fun v =>
      let R := fi24RelA X Xi Y Yi v
      eqA 378 R I || eqA 378 R Z || eqA 378 R Z2) &&
    !(eqA 378 X I || eqA 378 X Z || eqA 378 X Z2)

@[noinline, expose] def fi24ShapeCheck : Bool :=
  fi24SiftW fi24ShapeZ && fi24SiftW fi24ShapeX && fi24SiftW fi24ShapeY && fi24ShapeP

end CFSG.EvenSporadicStandard.TwoFi22.DS81
