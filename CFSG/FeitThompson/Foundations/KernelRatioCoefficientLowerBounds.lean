module

public import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.FieldSimp
public import Mathlib.Basic.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {p q : ℕ}

noncomputable def kernelRatioCoeff (p q : ℕ) : ℝ :=
  1 - 1 / ((q : ℝ) - 1) - ((q : ℝ) - 1) / (q : ℝ) ^ p + 1 / (((q : ℝ) - 1) * (q : ℝ) ^ p)

theorem kernelRatioCoeff_eq (p q : ℕ) :
    kernelRatioCoeff p q =
      1 - 1 / ((q : ℝ) - 1) - ((q : ℝ) - 1) / (q : ℝ) ^ p
        + 1 / (((q : ℝ) - 1) * (q : ℝ) ^ p) := (rfl)

theorem one_sub_lt_kernelRatioCoeff (hp : 3 ≤ p) (hq : 3 ≤ q) :
    1 - 1 / ((q : ℝ) - 1) - 1 / (q : ℝ) ^ 2 < kernelRatioCoeff p q := by
  have hq3 : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hQ1 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have hpow3 : (0 : ℝ) < (q : ℝ) ^ 3 := by positivity
  have hle : ((q : ℝ)) ^ 3 ≤ (q : ℝ) ^ p := pow_le_pow_right₀ (by linarith) hp
  have hpowp : (0 : ℝ) < (q : ℝ) ^ p := lt_of_lt_of_le hpow3 hle
  have h1 : ((q : ℝ) - 1) / (q : ℝ) ^ p ≤ ((q : ℝ) - 1) / (q : ℝ) ^ 3 := by gcongr
  have h2 : ((q : ℝ) - 1) / (q : ℝ) ^ 3 < 1 / (q : ℝ) ^ 2 := by
    rw [div_lt_div_iff₀ hpow3 (by positivity)]
    nlinarith
  have h3 : (0 : ℝ) < 1 / (((q : ℝ) - 1) * (q : ℝ) ^ p) := by positivity
  rw [kernelRatioCoeff_eq]
  linarith

theorem four_fifths_lt_kernelRatioCoeff (hp : 3 ≤ p) (hq : 7 ≤ q) :
    (4 / 5 : ℝ) < kernelRatioCoeff p q := by
  have hq7 : (7 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have h1 : 1 / ((q : ℝ) - 1) ≤ 1 / 6 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have h2 : 1 / (q : ℝ) ^ 2 ≤ 1 / 49 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have := one_sub_lt_kernelRatioCoeff hp (le_trans (by norm_num) hq)
  linarith

theorem seven_tenths_lt_kernelRatioCoeff (hp : 3 ≤ p) (hq : 5 ≤ q) :
    (7 / 10 : ℝ) < kernelRatioCoeff p q := by
  have hq5 : (5 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have h1 : 1 / ((q : ℝ) - 1) ≤ 1 / 4 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have h2 : 1 / (q : ℝ) ^ 2 ≤ 1 / 25 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have := one_sub_lt_kernelRatioCoeff hp (le_trans (by norm_num) hq)
  linarith

private theorem three_zpow_one_sub (p : ℕ) : (3 : ℝ) ^ (1 - (p : ℤ)) = 3 / 3 ^ p := by
  rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one, zpow_natCast]

theorem kernelRatioCoeff_three (p : ℕ) :
    kernelRatioCoeff p 3 = (1 - (3 : ℝ) ^ (1 - (p : ℤ))) / 2 := by
  have hp0 : (0 : ℝ) < 3 ^ p := by positivity
  rw [kernelRatioCoeff_eq, three_zpow_one_sub]
  norm_num
  field_simp
  ring

theorem fortyNine_hundredths_lt_kernelRatioCoeff_three (hp : 5 ≤ p) :
    (49 / 100 : ℝ) < kernelRatioCoeff p 3 := by
  have hpow : (243 : ℝ) ≤ 3 ^ p := by
    calc (243 : ℝ) = 3 ^ 5 := by norm_num
      _ ≤ 3 ^ p := pow_le_pow_right₀ (by norm_num) hp
  have h : (3 : ℝ) / 3 ^ p ≤ 3 / 243 := by gcongr
  rw [kernelRatioCoeff_three, three_zpow_one_sub]
  linarith

theorem kernelRatioCoeff_lower_bounds (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q) :
    (7 ≤ q → (4 / 5 : ℝ) < kernelRatioCoeff p q) ∧
      (5 ≤ q → (7 / 10 : ℝ) < kernelRatioCoeff p q) ∧
      (q = 3 → 5 ≤ p ∧ kernelRatioCoeff p 3 = (1 - (3 : ℝ) ^ (1 - (p : ℤ))) / 2 ∧
        (49 / 100 : ℝ) < kernelRatioCoeff p 3) := by
  have hp3 : 3 ≤ p := hp.odd_iff.mp (hp.odd_of_ne_two hp2)
  refine ⟨four_fifths_lt_kernelRatioCoeff hp3, seven_tenths_lt_kernelRatioCoeff hp3, fun hq3 => ?_⟩
  have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 (hq3 ▸ hpq)
  exact ⟨hp5, kernelRatioCoeff_three p, fortyNine_hundredths_lt_kernelRatioCoeff_three hp5⟩

end CFSG.FeitThompson
