module

public import CFSG.LieType.Chevalley.E6Three.StabilizerFour

public section

set_option autoImplicit false

namespace CFSG.LieType.Chevalley.E6Three.StabilizerN6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LieType.Chevalley.E6Three.ModelKernel CFSG.LieType.Chevalley.E6Three.StabilizerFour

theorem pairKey_toFun (b c : N6) : pairKey b.toFun c.toFun = N6.key b c := rfl

theorem positionBasis_three_zero : positionBasis 3 0 = N6.toFun ⟨1, 2, 1, 0, 0, 0⟩ := by
  decide +kernel

theorem positionBasis_three_one : positionBasis 3 1 = N6.toFun ⟨0, 0, 0, 1, 0, 0⟩ := by
  decide +kernel

end CFSG.LieType.Chevalley.E6Three.StabilizerN6
