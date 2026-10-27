module

public import CFSG.GH74.GLS.C3.Layer1.BkL27K
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools Blueprint

theorem exists_odd_two_mul_card_of_hasL2Model {H : Type} [Group H] (h : HasL2Model H Odd) :
    ∃ q : ℕ, Odd q ∧ 2 * Nat.card H = q * (q ^ 2 - 1) := by
  obtain ⟨p, f, hp, hf, hodd, hL⟩ := h
  exact ⟨p ^ f, hodd, C3.Layer1.Bk.two_mul_card_of_hasL2Model_eq hodd ⟨p, f, hp, hf, rfl, hL⟩⟩

theorem card_eq_of_lieModel_L34 {X : Type} [Group X] (h : LieModel X .PSL 3 2 2) :
    Nat.card X = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four (h.statedClassicalModel (by decide))

theorem no_q_mul_sq_sub_one_eq_5040 (q : ℕ) (h : q * (q ^ 2 - 1) = 5040) : False := by
  have hq : q ≤ 18 := by
    by_contra hcon
    push Not at hcon
    have : 19 * (19 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
      Nat.mul_le_mul hcon (Nat.sub_le_sub_right (Nat.pow_le_pow_left hcon 2) 1)
    omega
  interval_cases q <;> omega

theorem no_q_mul_sq_sub_one_eq_40320 (q : ℕ) (h : q * (q ^ 2 - 1) = 40320) : False := by
  have hq : q ≤ 36 := by
    by_contra hcon
    push Not at hcon
    have : 37 * (37 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
      Nat.mul_le_mul hcon (Nat.sub_le_sub_right (Nat.pow_le_pow_left hcon 2) 1)
    omega
  interval_cases q <;> omega

end CFSG.GH74.GLS
