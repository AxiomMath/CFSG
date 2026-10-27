module

public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.HardMathSupport.Lang.AnisoF4

theorem not_dvd_of_zmod_ne_zero {P n : ℕ} (h : ((n : ℕ) : ZMod P) ≠ 0) : ¬ P ∣ n :=
  fun hd => h ((ZMod.natCast_eq_zero_iff n P).2 hd)

theorem notDvd_facts {P q : ℕ} (hP : P.Prime) (hP5 : 5 ≤ P) (hq : 1 ≤ q)
    (hd : P ∣ q ^ 2 + 1) :
    (∀ k : ℕ, ¬ P ∣ q ^ k) ∧ ¬ P ∣ q ^ 2 - 1 ∧ ¬ P ∣ q ^ 6 - 1 ∧ ¬ P ∣ q ^ 8 + q ^ 4 + 1 := by
  haveI := Fact.mk hP
  have hz2 : (2 : ZMod P) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod P) = 0 := by exact_mod_cast h
    have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 2 P).1 this)
    omega
  have hz3 : (3 : ZMod P) ≠ 0 := by
    intro h
    have : ((3 : ℕ) : ZMod P) = 0 := by exact_mod_cast h
    have := (Nat.prime_dvd_prime_iff_eq hP Nat.prime_three).1 ((ZMod.natCast_eq_zero_iff 3 P).1 this)
    omega
  have hsq : ((q : ZMod P)) ^ 2 = -1 := by
    have : ((q ^ 2 + 1 : ℕ) : ZMod P) = 0 := (ZMod.natCast_eq_zero_iff _ P).2 hd
    push_cast at this
    linear_combination this
  have hq0 : (q : ZMod P) ≠ 0 := by
    intro h
    rw [h] at hsq
    norm_num at hsq
  have hqpos : ∀ k : ℕ, 1 ≤ q ^ k := fun k => Nat.one_le_pow _ _ (by omega)
  refine ⟨fun k => not_dvd_of_zmod_ne_zero (by push_cast; exact pow_ne_zero _ hq0), ?_, ?_, ?_⟩
  · refine not_dvd_of_zmod_ne_zero (by
      rw [Nat.cast_sub (hqpos 2)]
      push_cast
      rw [hsq]
      intro h
      apply hz2
      linear_combination -h)
  · refine not_dvd_of_zmod_ne_zero (by
      rw [Nat.cast_sub (hqpos 6)]
      push_cast
      have : (q : ZMod P) ^ 6 = -1 := by
        calc (q : ZMod P) ^ 6 = ((q : ZMod P) ^ 2) ^ 3 := by ring
          _ = -1 := by rw [hsq]; norm_num
      rw [this]
      intro h
      apply hz2
      linear_combination -h)
  · refine not_dvd_of_zmod_ne_zero (by
      push_cast
      have h4 : (q : ZMod P) ^ 4 = 1 := by
        calc (q : ZMod P) ^ 4 = ((q : ZMod P) ^ 2) ^ 2 := by ring
          _ = 1 := by rw [hsq]; norm_num
      have h8 : (q : ZMod P) ^ 8 = 1 := by
        calc (q : ZMod P) ^ 8 = ((q : ZMod P) ^ 4) ^ 2 := by ring
          _ = 1 := by rw [h4]; norm_num
      rw [h8, h4]
      intro h
      apply hz3
      linear_combination h)

end CFSG.HardMathSupport.Lang.AnisoF4
