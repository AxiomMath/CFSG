module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.HardMathSupport.Lang.Proving

theorem exists_ne_one_pow_three_of_three_dvd (K : Type*) [Field K] [Finite K]
    (h : 3 ∣ Nat.card K - 1) : ∃ ζ : Kˣ, ζ ≠ 1 ∧ ζ ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units]
    exact h
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' 3 hcard
  refine ⟨ζ, ?_, ?_⟩
  · rintro rfl
    rw [orderOf_one] at hζ
    exact absurd hζ (by norm_num)
  · rw [← hζ]
    exact pow_orderOf_eq_one ζ

end CFSG.HardMathSupport.Lang.Proving
