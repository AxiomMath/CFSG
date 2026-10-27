module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Proving

public theorem natCard_SL4_field (F : Type*) [Field F] [Fintype F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 4) F) =
      Fintype.card F ^ 6 * (Fintype.card F ^ 2 - 1) * (Fintype.card F ^ 3 - 1) *
        (Fintype.card F ^ 4 - 1) := by
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_four]
  rw [show ((3 : Fin 4) : ℕ) = 3 from rfl]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  generalize Fintype.card F = q at hq ⊢
  have e1 : 1 ≤ q := by omega
  have e2 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  have e3 : q ^ 2 ≤ q ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have e4 : q ^ 3 ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have e5 : q ≤ q ^ 4 := le_trans e2 (le_trans e3 e4)
  have e6 : q ^ 2 ≤ q ^ 4 := le_trans e3 e4
  have e7 : 1 ≤ q ^ 4 := le_trans e1 e5
  have e8 : 1 ≤ q ^ 2 := le_trans e1 e2
  have e9 : 1 ≤ q ^ 3 := le_trans e1 (le_trans e2 e3)
  apply Nat.div_eq_of_eq_mul_left (by omega)
  zify [e1, e2, e3, e4, e5, e6, e7, e8, e9]
  ring

end CFSG.HardMathSupport.Foote.Proving
