module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.HardMathSupport.Malle.Proving

theorem orderOf_eq_three_of_dvd {p q : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (h : p ∣ q ^ 2 + q + 1) : orderOf ((q : ℕ) : ZMod p) = 3 := by
  have : Fact p.Prime := ⟨hp⟩
  have hx : ((q : ℕ) : ZMod p) ^ 2 + ((q : ℕ) : ZMod p) + 1 = 0 := by
    have := (ZMod.natCast_eq_zero_iff (q ^ 2 + q + 1) p).2 h
    push_cast at this
    exact this
  generalize ((q : ℕ) : ZMod p) = x at hx ⊢
  have hx3 : x ^ 3 = 1 := by
    linear_combination (x - 1) * hx
  have hx1 : x ≠ 1 := by
    intro h1
    rw [h1] at hx
    have h3 : ((3 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination hx
    rw [ZMod.natCast_eq_zero_iff] at h3
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3)
  have hdvd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h1
  · exact absurd (orderOf_eq_one_iff.1 h1) hx1
  · exact h1

theorem orderOf_eq_six_of_dvd {p q : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (h : p ∣ q ^ 2 - q + 1) : orderOf ((q : ℕ) : ZMod p) = 6 := by
  have : Fact p.Prime := ⟨hp⟩
  have hle : q ≤ q ^ 2 := Nat.le_self_pow two_ne_zero q
  have hx : ((q : ℕ) : ZMod p) ^ 2 - ((q : ℕ) : ZMod p) + 1 = 0 := by
    have := (ZMod.natCast_eq_zero_iff (q ^ 2 - q + 1) p).2 h
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hle, Nat.cast_pow] at this
    exact this
  have hp2 : p ≠ 2 := by
    rintro rfl
    revert hx
    generalize ((q : ℕ) : ZMod 2) = y
    revert y
    decide
  generalize ((q : ℕ) : ZMod p) = x at hx ⊢
  have hx3 : x ^ 3 = -1 := by
    linear_combination (x + 1) * hx
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
  have h6 : x ^ 6 = 1 := by
    calc x ^ 6 = (x ^ 3) ^ 2 := by ring
      _ = 1 := by rw [hx3]; norm_num
  have hdvd6 : orderOf x ∣ 6 := orderOf_dvd_of_pow_eq_one h6
  have hpos : 0 < orderOf x := by
    refine Nat.pos_of_ne_zero (fun h0 => ?_)
    rw [h0] at hdvd6
    norm_num at hdvd6
  have hne1 : orderOf x ≠ 1 := by
    intro h1
    rw [orderOf_eq_one_iff] at h1
    rw [h1] at hx
    norm_num at hx
  have hne2 : orderOf x ≠ 2 := by
    intro h2o
    have hsq : x ^ 2 = 1 := by
      have := pow_orderOf_eq_one x
      rwa [h2o] at this
    have hxm : x = -1 := by
      linear_combination hx3 - x * hsq
    have h3z : (3 : ZMod p) = 0 := by
      rw [hxm] at hx
      linear_combination hx
    have h3n : ((3 : ℕ) : ZMod p) = 0 := by
      exact_mod_cast h3z
    rw [ZMod.natCast_eq_zero_iff] at h3n
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3n)
  have hne3 : orderOf x ≠ 3 := by
    intro h3o
    have := pow_orderOf_eq_one x
    rw [h3o, hx3] at this
    apply h2
    linear_combination -this
  generalize orderOf x = e at hdvd6 hpos hne1 hne2 hne3 ⊢
  have hle6 : e ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd6
  interval_cases e <;> omega

theorem not_int_dvd_sub_one_mul_add_one_of_orderOf {p q e : ℕ} (hp : p.Prime)
    (he : orderOf ((q : ℕ) : ZMod p) = e) (he1 : e ≠ 1) (he2 : e ≠ 2) :
    ¬ (p : ℤ) ∣ ((q : ℤ) - 1) * ((q : ℤ) + 1) := by
  intro hd
  have : Fact p.Prime := ⟨hp⟩
  have h0 : ((((q : ℤ) - 1) * ((q : ℤ) + 1) : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hd
  push_cast at h0
  have hsq : ((q : ℕ) : ZMod p) ^ 2 = 1 := by
    linear_combination h0
  have hord : orderOf ((q : ℕ) : ZMod p) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  rw [he] at hord
  have hle : e ≤ 2 := Nat.le_of_dvd (by norm_num) hord
  interval_cases e <;> omega

end CFSG.HardMathSupport.Malle.Proving
