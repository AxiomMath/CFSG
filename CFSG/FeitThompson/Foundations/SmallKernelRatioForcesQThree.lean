module

public import CFSG.FeitThompson.Foundations.KernelRatioCoefficientLowerBounds
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {p q : ℕ}

private theorem ratio_lt_three_quarters_of_p_eq_three {Q : ℝ} (hQ : 3 ≤ Q) :
    Q * 3 / ((2 * Q + 1) * (3 - 1)) < 3 / 4 := by
  have hd : (0 : ℝ) < (2 * Q + 1) * (3 - 1) := by nlinarith
  rw [div_lt_div_iff₀ hd (by norm_num)]
  nlinarith

private theorem ratio_lt_five_eighths {P Q : ℝ} (hP : 5 ≤ P) (hQ : 5 ≤ Q) :
    Q * P / ((2 * Q + 1) * (P - 1)) < 5 / 8 := by
  have hd : (0 : ℝ) < (2 * Q + 1) * (P - 1) := by nlinarith
  rw [div_lt_div_iff₀ hd (by norm_num)]
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ Q) (by linarith : (0:ℝ) ≤ P - 5)]

theorem eq_three_and_five_le_of_kernelRatioCoeff_lt
    (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p ≠ q)
    (h : kernelRatioCoeff p q < (q : ℝ) * p / ((2 * (q : ℝ) + 1) * ((p : ℝ) - 1))) :
    q = 3 ∧ 5 ≤ p := by
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  have hqodd : q % 2 = 1 := Nat.odd_iff.mp (hq.odd_of_ne_two hq2)
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  have hqR : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
  have hp5 : 5 ≤ p := by
    rcases eq_or_lt_of_le hp3 with h3 | h4
    · exfalso
      have hpe : (p : ℝ) = 3 := by rw [← h3]; norm_num
      have hq5 : 5 ≤ q := by
        have : q ≠ 3 := fun hq3' => hpq (by omega)
        omega
      rcases (by omega : q = 5 ∨ 7 ≤ q) with hq5' | hq7
      · have hb : (q : ℝ) * p / ((2 * (q : ℝ) + 1) * ((p : ℝ) - 1)) < 7 / 10 := by
          have hqe : (q : ℝ) = 5 := by rw [hq5']; norm_num
          rw [hqe, hpe]; norm_num
        have hlow := seven_tenths_lt_kernelRatioCoeff (p := p) (q := q) hp3 hq5
        linarith
      · have hb : (q : ℝ) * p / ((2 * (q : ℝ) + 1) * ((p : ℝ) - 1)) < 3 / 4 := by
          rw [hpe]; exact ratio_lt_three_quarters_of_p_eq_three hqR
        have hlow := four_fifths_lt_kernelRatioCoeff (p := p) (q := q) hp3 hq7
        linarith
    · omega
  refine ⟨?_, hp5⟩
  have hq5 : q < 5 := by
    by_contra hcon
    have hq5' : 5 ≤ q := by omega
    have hpR : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp5
    have hqR5 : (5 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq5'
    have hb := ratio_lt_five_eighths hpR hqR5
    have hlow := seven_tenths_lt_kernelRatioCoeff (p := p) (q := q) hp3 hq5'
    linarith
  omega

end CFSG.FeitThompson
