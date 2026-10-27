module

public import CFSG.LargeExtraspecial.AS35WQP45Data

public section

namespace CFSG.LargeExtraspecial

open CFSG.GH74.KGroups CFSG.GH74.KGroups.NativeChecks CFSG.Monster.B.Co2.Native
  CFSG.ComponentClassification.CatFactsSmall.PSp43

namespace AS35W

@[expose] def cube1A45 (y : Array Nat) : Bool := eqA 45 (compA 45 y (compA 45 y y)) (idA 45)

@[expose] def qp45W2CheckL (L : List (Array Nat)) : Bool :=
  let L3 := L.filter cube1A45
  L.all fun s => !invA45 s ||
    let C3 := L3.filter fun y => eqA 45 (compA 45 y s) (compA 45 s y)
    C3.any fun y₁ => C3.any fun y₂ => !cube1A45 (compA 45 y₁ y₂)

@[expose] def qp45W2Check (_ : Unit := ()) : Bool := qp45W2CheckL (enumA QP45)

end AS35W

end CFSG.LargeExtraspecial
