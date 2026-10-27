module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Rat.Defs
public import Mathlib.GroupTheory.Index
import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

theorem exceptionalU_eq : (5 ^ 3 - 1) / (5 - 1) = 31 := by norm_num

theorem exceptionalV_eq : (3 ^ 5 - 1) / (3 - 1) = 121 := by norm_num

theorem le_natCard_of_natCard_eq_31 {H : Type*} [Group H] [Finite H] {U : Subgroup H}
    (hU : Nat.card U = 31) (hH : (Nat.card H : ℤ) ≡ 1 [ZMOD 5 * 3]) (hne : U ≠ ⊤) :
    496 ≤ Nat.card H := by
  have hcard : Nat.card H = U.index * 31 := by
    rw [natCard_eq_natCard_range_leftCoset_mul_natCard U, natCard_range_leftCoset U, hU]
  have h0 : U.index ≠ 0 := U.index_ne_zero_of_finite
  have h1 : U.index ≠ 1 := fun h => hne (Subgroup.index_eq_one.mp h)
  have hx : (2 : ℤ) ≤ (U.index : ℤ) := by
    have : 2 ≤ U.index := by omega
    exact_mod_cast this
  have hdvd : (15 : ℤ) ∣ (Nat.card H : ℤ) - 1 := by simpa using Int.ModEq.dvd hH.symm
  have hcardZ : (Nat.card H : ℤ) = (U.index : ℤ) * 31 := by exact_mod_cast hcard
  have : (496 : ℤ) ≤ (Nat.card H : ℤ) := by omega
  exact_mod_cast this

theorem exceptional_support_degree_gap {H : Type*} [Group H] [Finite H] {U : Subgroup H}
    (hU : Nat.card U = (5 ^ 3 - 1) / (5 - 1)) (hH : (Nat.card H : ℤ) ≡ 1 [ZMOD 5 * 3])
    (hne : U ≠ ⊤) :
    (((5 ^ 3 - 1) / (5 - 1) : ℚ) - 1) / 3 = 10 ∧ (((3 ^ 5 - 1) / (3 - 1) : ℚ) - 1) / 5 = 24 ∧
      (((5 ^ 3 - 1) / (5 - 1) : ℚ) - 1) / 3 < (((3 ^ 5 - 1) / (3 - 1) : ℚ) - 1) / 5 ∧
        (((3 ^ 5 - 1) / (3 - 1) : ℚ) - 1) / 5 < ((Nat.card H : ℚ) - 1) / (5 * 3) := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  have h496 : (496 : ℚ) ≤ (Nat.card H : ℚ) := by
    exact_mod_cast le_natCard_of_natCard_eq_31 (by rwa [exceptionalU_eq] at hU) hH hne
  rw [show (((3 : ℚ) ^ 5 - 1) / (3 - 1) - 1) / 5 = 24 by norm_num,
    lt_div_iff₀ (by norm_num : (0 : ℚ) < 5 * 3)]
  linarith

theorem le_natCard_sub_one_div {H : Type*} [Group H] [Finite H] {U : Subgroup H}
    (hU : Nat.card U = 31) (hH : (Nat.card H : ℤ) ≡ 1 [ZMOD 5 * 3]) (hne : U ≠ ⊤) :
    (33 : ℚ) ≤ ((Nat.card H : ℚ) - 1) / (5 * 3) := by
  have h496 : (496 : ℚ) ≤ (Nat.card H : ℚ) := by
    exact_mod_cast le_natCard_of_natCard_eq_31 hU hH hne
  rw [le_div_iff₀ (by norm_num : (0 : ℚ) < 5 * 3)]
  linarith

end

end CFSG.FeitThompson
