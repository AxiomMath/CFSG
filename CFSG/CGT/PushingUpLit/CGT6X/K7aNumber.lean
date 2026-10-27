module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.CGT.PushingUpLit.CGT6X.K7a

section ZModFacts

variable {p : ℕ} [Fact p.Prime]

theorem sq_add_one_facts (hp2 : p ≠ 2) {x : ZMod p} (hx : x ^ 2 + 1 = 0) :
    x ≠ 0 ∧ x - 1 ≠ 0 ∧ x + 1 ≠ 0 ∧ x ^ 2 - 1 ≠ 0 ∧ x ^ 3 - 1 ≠ 0 ∧ x ^ 3 + 1 ≠ 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 (by exact_mod_cast h)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1 this)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [h] at hx
    norm_num at hx
  · intro h
    apply h2
    have h1 : x = 1 := by linear_combination h
    rw [h1] at hx
    linear_combination hx
  · intro h
    apply h2
    have h1 : x = -1 := by linear_combination h
    rw [h1] at hx
    linear_combination hx
  · intro h
    apply h2
    linear_combination (-1 : ZMod p) * h + hx
  · intro h
    apply h2
    have h1 : x + 1 = 0 := by linear_combination x * hx - h
    have h3 : x = -1 := by linear_combination h1
    rw [h3] at hx
    linear_combination hx
  · intro h
    apply h2
    have h1 : x - 1 = 0 := by linear_combination x * hx - h
    have h3 : x = 1 := by linear_combination h1
    rw [h3] at hx
    linear_combination hx

end ZModFacts

variable {p r : ℕ}

theorem not_dvd_GL3 (hp : p.Prime) (hp2 : p ≠ 2) (hr : 2 ≤ r) (hpr : p ∣ r ^ 2 + 1) :
    ¬ p ∣ (r ^ 3 - 1) * (r ^ 3 - r) * (r ^ 3 - r ^ 2) := by
  have : Fact p.Prime := ⟨hp⟩
  intro h
  have hx : ((r : ZMod p)) ^ 2 + 1 = 0 := by
    have := (ZMod.natCast_eq_zero_iff (r ^ 2 + 1) p).2 hpr
    exact_mod_cast this
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := sq_add_one_facts hp2 hx
  have h1' : 1 ≤ r ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h2' : r ≤ r ^ 3 := by
    calc r = r ^ 1 := (pow_one r).symm
      _ ≤ r ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h3' : r ^ 2 ≤ r ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hz := (ZMod.natCast_eq_zero_iff _ p).2 h
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub h1', Nat.cast_sub h2', Nat.cast_sub h3'] at hz
  push_cast at hz
  have hr0 : (r : ZMod p) ≠ 0 := h0
  have hfac : ((r : ZMod p) ^ 3 - 1) * ((r : ZMod p) ^ 3 - r) *
      ((r : ZMod p) ^ 3 - (r : ZMod p) ^ 2) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero h4 ?_) ?_
    · have : (r : ZMod p) ^ 3 - r = r * (r ^ 2 - 1) := by ring
      rw [this]
      exact mul_ne_zero hr0 h3
    · have : (r : ZMod p) ^ 3 - r ^ 2 = r ^ 2 * (r - 1) := by ring
      rw [this]
      exact mul_ne_zero (pow_ne_zero 2 hr0) h1
  exact hfac hz

theorem not_dvd_SU3 (hp : p.Prime) (hp2 : p ≠ 2) (hr : 2 ≤ r) (hpr : p ∣ r ^ 2 + 1) :
    ¬ p ∣ r ^ 3 * (r ^ 2 - 1) * (r ^ 3 + 1) := by
  have : Fact p.Prime := ⟨hp⟩
  intro h
  have hx : ((r : ZMod p)) ^ 2 + 1 = 0 := by
    have := (ZMod.natCast_eq_zero_iff (r ^ 2 + 1) p).2 hpr
    exact_mod_cast this
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := sq_add_one_facts hp2 hx
  have h3' : 1 ≤ r ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hz := (ZMod.natCast_eq_zero_iff _ p).2 h
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub h3'] at hz
  push_cast at hz
  have hfac : (r : ZMod p) ^ 3 * ((r : ZMod p) ^ 2 - 1) * ((r : ZMod p) ^ 3 + 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero 3 h0) h3) h5
  exact hfac hz

end CFSG.CGT.PushingUpLit.CGT6X.K7a
