module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.HardMathSupport.Foote.Proving

theorem card_SL_two_five : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) = 120 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h := Matrix.card_SL_field (𝔽 := ZMod 5) 2
  rw [ZMod.card] at h
  refine h.trans ?_
  norm_num [Fin.prod_univ_two]

end CFSG.HardMathSupport.Foote.Proving
