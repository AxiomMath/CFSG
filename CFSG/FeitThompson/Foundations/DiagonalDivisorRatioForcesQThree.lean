module

public import CFSG.FeitThompson.Foundations.KernelRatioCoefficientLowerBounds
import CFSG.FeitThompson.Foundations.QThreeQuadraticOrderThreshold
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {p q A u : ℕ}

theorem sixteen_mul_succ_le_five_mul_two_pow {k : ℕ} (hk : 4 ≤ k) :
    16 * (k + 1) ≤ 5 * 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h : (16 : ℕ) ≤ 5 * 2 ^ n := by
      have h2 : (2 : ℕ) ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      calc (16 : ℕ) = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ n := h2
        _ ≤ 5 * 2 ^ n := by omega
    rw [pow_succ]
    linarith [ih, h]

theorem eq_three_of_ratio_lt (hq : q.Prime) (hq2 : q ≠ 2) (hp3 : 3 ≤ p)
    (hA : p = 2 * A + 1) (hdvd : u ∣ A ^ (q - 1))
    (hlt : kernelRatioCoeff p q * (p : ℝ) ^ (q - 1) / q < u) : q = 3 := by
  by_contra hq3
  have hq5 : 5 ≤ q := hq.five_le_of_ne_two_of_ne_three hq2 hq3
  have hA1 : 1 ≤ A := by omega
  have hm : (7 / 10 : ℝ) < kernelRatioCoeff p q := seven_tenths_lt_kernelRatioCoeff hp3 hq5
  have hApos : 0 < A ^ (q - 1) := pow_pos hA1 _
  have huA : u ≤ A ^ (q - 1) := Nat.le_of_dvd hApos hdvd
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
  have hk4 : 4 ≤ k := by omega
  simp only [Nat.add_sub_cancel] at hlt huA
  set m := kernelRatioCoeff p (k + 1) with hmdef
  have hQ : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hP : (0 : ℝ) < (p : ℝ) ^ k := by positivity
  have hT : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hcast : (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 := by push_cast; ring
  rw [hcast, div_lt_iff₀ hQ] at hlt
  have h2 : (u : ℝ) ≤ (A : ℝ) ^ k := by exact_mod_cast huA
  have h3 : (2 : ℝ) ^ k * (A : ℝ) ^ k < (p : ℝ) ^ k := by
    have hpA : (2 : ℝ) * (A : ℝ) < (p : ℝ) := by
      have : (p : ℝ) = 2 * (A : ℝ) + 1 := by rw [hA]; push_cast; ring
      linarith
    calc (2 : ℝ) ^ k * (A : ℝ) ^ k = (2 * (A : ℝ)) ^ k := by rw [mul_pow]
      _ < (p : ℝ) ^ k := pow_lt_pow_left₀ hpA (by positivity) (by omega)
  have h4 : (16 : ℝ) * ((k : ℝ) + 1) ≤ 5 * (2 : ℝ) ^ k := by
    have h5 := sixteen_mul_succ_le_five_mul_two_pow hk4
    have h6 : ((16 * (k + 1) : ℕ) : ℝ) ≤ ((5 * 2 ^ k : ℕ) : ℝ) := by exact_mod_cast h5
    push_cast at h6
    linarith
  have step2 : (2 : ℝ) ^ k * (u : ℝ) < (p : ℝ) ^ k :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left h2 hT.le) h3
  have step3 : m * (p : ℝ) ^ k * (2 : ℝ) ^ k < (p : ℝ) ^ k * ((k : ℝ) + 1) := by
    calc m * (p : ℝ) ^ k * (2 : ℝ) ^ k < ((u : ℝ) * ((k : ℝ) + 1)) * (2 : ℝ) ^ k :=
          mul_lt_mul_of_pos_right hlt hT
      _ = ((2 : ℝ) ^ k * (u : ℝ)) * ((k : ℝ) + 1) := by ring
      _ < (p : ℝ) ^ k * ((k : ℝ) + 1) := mul_lt_mul_of_pos_right step2 hQ
  nlinarith [mul_pos hP hT, mul_le_mul_of_nonneg_left h4 hP.le]

theorem eq_sq_of_ratio_lt (hp5 : 5 ≤ p) (hA : p = 2 * A + 1) (hdvd : u ∣ A ^ 2)
    (hlt : kernelRatioCoeff p 3 * (p : ℝ) ^ 2 / 3 < u) : u = A ^ 2 := by
  have hA2 : 2 ≤ A := by omega
  rw [kernelRatioCoeff_three] at hlt
  have hthr : ((p : ℝ) ^ 2 - 1) / 6 < u :=
    sq_sub_one_div_six_lt_of_ratio_mul_sq_div_three_lt hp5 hlt
  by_contra hne
  have hApos : 0 < A ^ 2 := by positivity
  obtain ⟨c, hc⟩ := hdvd
  have hc2 : 2 ≤ c := by
    rcases Nat.lt_or_ge c 2 with h | h
    · interval_cases c
      · simp only [Nat.mul_zero] at hc; exact absurd hc hApos.ne'
      · rw [mul_one] at hc; exact absurd hc.symm hne
    · exact h
  have h2u : 2 * u ≤ A ^ 2 := by
    rw [hc]
    calc 2 * u = u * 2 := by ring
      _ ≤ u * c := Nat.mul_le_mul_left u hc2
  have hpR : (p : ℝ) = 2 * (A : ℝ) + 1 := by rw [hA]; push_cast; ring
  have h2uR : 2 * (u : ℝ) ≤ (A : ℝ) ^ 2 := by exact_mod_cast h2u
  have hAR : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA2
  rw [hpR] at hthr
  nlinarith [hthr, h2uR, hAR]

theorem eq_three_and_eq_sq_of_ratio_lt (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (hpq : p ≠ q) (hdvd : u ∣ ((p - 1) / 2) ^ (q - 1))
    (hlt : kernelRatioCoeff p q * (p : ℝ) ^ (q - 1) / q < u) :
    q = 3 ∧ u = ((p - 1) / 2) ^ 2 := by
  have hp3 : 3 ≤ p := hp.odd_iff.mp (hp.odd_of_ne_two hp2)
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  have hA : p = 2 * ((p - 1) / 2) + 1 := by omega
  have hq3 : q = 3 := eq_three_of_ratio_lt hq hq2 hp3 hA hdvd hlt
  subst hq3
  refine ⟨rfl, ?_⟩
  have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hpq
  norm_num at hdvd hlt
  exact eq_sq_of_ratio_lt hp5 hA hdvd hlt

end CFSG.FeitThompson
