module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import CFSG.HardMathSupport.Foote.Proving.CoverThree.Valuation

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Proving

public theorem natCard_SL3_field (F : Type*) [Field F] [Fintype F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) =
      Fintype.card F ^ 3 * (Fintype.card F ^ 2 - 1) * (Fintype.card F ^ 3 - 1) := by
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  generalize Fintype.card F = q at hq ⊢
  have e1 : 1 ≤ q := by omega
  have e2 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  have e3 : q ^ 2 ≤ q ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have e4 : q ≤ q ^ 3 := le_trans e2 e3
  have e5 : 1 ≤ q ^ 3 := le_trans e1 e4
  have e6 : 1 ≤ q ^ 2 := le_trans e1 e2
  apply Nat.div_eq_of_eq_mul_left (by omega)
  zify [e1, e2, e3, e4, e5, e6]
  ring

public theorem padicValNat_three_natCard_SL3_of_three_cover (F : Type*) [Field F] [Fintype F]
    (h3 : 3 ∣ Fintype.card F - 1) (h9 : ¬ 9 ∣ Fintype.card F - 1) :
    padicValNat 3 (Nat.card (Matrix.SpecialLinearGroup (Fin 3) F)) = 3 := by
  rw [natCard_SL3_field]
  exact three_part_SL3_of_three_cover _ Fintype.one_lt_card h3 h9

end CFSG.HardMathSupport.Foote.Proving
