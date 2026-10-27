module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import CFSG.HardMathSupport.Foote.Proving.OrderSL4

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Proving

public theorem natCard_center_SL_le (n : Type*) [Fintype n] [DecidableEq n] (F : Type*) [Field F] :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup n F)) ≤ max (Fintype.card n) 1 := by
  have e := Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity (n := n) (R := F)
  have : NeZero (max (Fintype.card n) 1) := ⟨by omega⟩
  exact (Nat.card_congr e.toEquiv).trans_le (card_rootsOfUnity _ _)

end CFSG.HardMathSupport.Foote.Proving
