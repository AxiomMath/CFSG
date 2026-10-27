module

public import CFSG.GH74.KGroups.NativeChecks2
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43ModelData

public section

namespace CFSG.LargeExtraspecial

open CFSG.GH74.KGroups CFSG.GH74.KGroups.NativeChecks CFSG.Monster.B.Co2.Native
  CFSG.ComponentClassification.CatFactsSmall.PSp43

namespace AS35W

@[expose] def invA45 (s : Array Nat) : Bool :=
  eqA 45 (compA 45 s s) (idA 45) && !eqA 45 s (idA 45)

@[expose] def qp45InvCheckL (L : List (Array Nat)) (xA : Array Nat) : Bool :=
  L.all fun s => !invA45 s || (L.any fun g => eqA 45 (compA 45 g xA) (compA 45 s g)) ||
    !decide (64 ∣ (L.filter fun g => eqA 45 (compA 45 g s) (compA 45 s g)).length)

@[expose] def qp45InvCheck : Bool := qp45InvCheckL (enumA QP45) (toA x45)

@[expose] def ord123A45 (c : Array Nat) : Bool :=
  eqA 45 c (idA 45) || eqA 45 (compA 45 c c) (idA 45) || eqA 45 (compA 45 c (compA 45 c c)) (idA 45)

@[expose] def qp45ProdCheckL (L : List (Array Nat)) (xA : Array Nat) : Bool :=
  L.all fun g => isInvA 45 g (invCand 45 g) &&
    ord123A45 (compA 45 xA (compA 45 (compA 45 g xA) (invCand 45 g)))

@[expose] def qp45ProdCheck : Bool := qp45ProdCheckL (enumA QP45) (toA x45)

end AS35W

end CFSG.LargeExtraspecial
