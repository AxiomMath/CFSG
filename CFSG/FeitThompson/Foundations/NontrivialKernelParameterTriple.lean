module

public import CFSG.FeitThompson.Foundations.KernelRatioCoefficientLowerBounds
import CFSG.FeitThompson.Foundations.SmallKernelRatioForcesQThree
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {p q : ℕ}

private theorem ratio_lt_ratio_of_le {Q P A C : ℝ} (hQ : 3 ≤ Q) (hP : 3 ≤ P) (hA : 1 ≤ A)
    (hC : 2 * Q + 1 ≤ C) :
    Q * ((P * A - 1) / (P - 1)) / (C * A) < Q * P / ((2 * Q + 1) * (P - 1)) := by
  have hP1 : (0 : ℝ) < P - 1 := by linarith
  have hA0 : (0 : ℝ) < A := by linarith
  have hd1 : (0 : ℝ) < C * A := by nlinarith
  have hd2 : (0 : ℝ) < (2 * Q + 1) * (P - 1) := by nlinarith
  rw [div_lt_div_iff₀ hd1 hd2]
  have hy : ((P * A - 1) / (P - 1)) * (P - 1) = P * A - 1 := div_mul_cancel₀ _ (ne_of_gt hP1)
  have hmul := mul_le_mul_of_nonneg_left hC (by positivity : (0 : ℝ) ≤ Q * P * A)
  calc Q * ((P * A - 1) / (P - 1)) * ((2 * Q + 1) * (P - 1))
      = Q * (2 * Q + 1) * (((P * A - 1) / (P - 1)) * (P - 1)) := by ring
    _ = Q * (2 * Q + 1) * (P * A - 1) := by rw [hy]
    _ < Q * (2 * Q + 1) * (P * A) := by nlinarith
    _ ≤ Q * P * (C * A) := by linarith

theorem eq_three_five_seven_of_kernelRatioCoeff_lt {c : ℤ}
    (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p ≠ q)
    (hc1 : 1 < c) (hcp : Int.gcd c p = 1) (hcq : 2 * (q : ℤ) ∣ c - 1)
    (h : kernelRatioCoeff p q <
      (q : ℝ) * (((p : ℝ) ^ q - 1) / ((p : ℝ) - 1)) / ((c : ℝ) * (p : ℝ) ^ (q - 1))) :
    q = 3 ∧ p = 5 ∧ c = 7 := by
  have hp3 : 3 ≤ p := by have := hp.two_le; have := Nat.odd_iff.mp (hp.odd_of_ne_two hp2); omega
  have hq3 : 3 ≤ q := by have := hq.two_le; have := Nat.odd_iff.mp (hq.odd_of_ne_two hq2); omega
  have hPR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  have hQR : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
  have hcz : 2 * (q : ℤ) + 1 ≤ c := by
    have := Int.le_of_dvd (by omega) hcq
    omega
  have hCR : 2 * (q : ℝ) + 1 ≤ (c : ℝ) := by exact_mod_cast hcz
  have hA1 : (1 : ℝ) ≤ (p : ℝ) ^ (q - 1) := one_le_pow₀ (by linarith)
  have hPA : (p : ℝ) ^ q = (p : ℝ) * (p : ℝ) ^ (q - 1) := by
    conv_lhs => rw [show q = (q - 1) + 1 from by omega]
    rw [pow_succ']
  have h' : kernelRatioCoeff p q < (q : ℝ) * p / ((2 * (q : ℝ) + 1) * ((p : ℝ) - 1)) := by
    refine lt_trans h ?_
    rw [hPA]
    exact ratio_lt_ratio_of_le hQR hPR hA1 hCR
  obtain ⟨hq3', hp5⟩ := eq_three_and_five_le_of_kernelRatioCoeff_lt hp hq hp2 hq2 hpq h'
  subst hq3'
  have hP1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hP5 : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp5
  have hval : ((p : ℝ) ^ (3 : ℕ) - 1) / ((p : ℝ) - 1) = (p : ℝ) ^ 2 + p + 1 := by
    rw [div_eq_iff (ne_of_gt hP1)]; ring
  have hlow := fortyNine_hundredths_lt_kernelRatioCoeff_three hp5
  have hkey : (49 / 100 : ℝ) < 3 * ((p : ℝ) ^ 2 + p + 1) / ((c : ℝ) * (p : ℝ) ^ 2) := by
    have h2 := lt_trans hlow h
    rw [hval, show (3 : ℕ) - 1 = 2 from rfl] at h2
    push_cast at h2
    exact h2
  have hCP : (0 : ℝ) < (c : ℝ) * (p : ℝ) ^ 2 := by
    have : (0 : ℝ) < (c : ℝ) := by push_cast at hCR ⊢; linarith
    positivity
  rw [lt_div_iff₀ hCP] at hkey
  have hc7 : c = 7 := by
    rcases (by omega : c = 7 ∨ 13 ≤ c) with h7 | h13
    · exact h7
    · exfalso
      have hCR13 : (13 : ℝ) ≤ (c : ℝ) := by exact_mod_cast h13
      nlinarith [mul_le_mul_of_nonneg_right hCR13 (sq_nonneg (p : ℝ)), sq_nonneg ((p : ℝ) - 5)]
  subst hc7
  have hp11 : p < 11 := by
    by_contra hcon
    have hPR11 : (11 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 11 ≤ p)
    norm_num at hkey
    nlinarith [sq_nonneg ((p : ℝ) - 11)]
  have hp57 : p = 5 ∨ p = 7 := by
    interval_cases p
    · exact Or.inl rfl
    · exact absurd hp (by norm_num)
    · exact Or.inr rfl
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
  rcases hp57 with h5 | h7
  · exact ⟨rfl, h5, rfl⟩
  ·
    exact absurd (h7 ▸ hcp) (by norm_num [Int.gcd])

end CFSG.FeitThompson
