module


public import Mathlib.Analysis.SpecialFunctions.Pow.Real

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.WidthArithmetic

theorem bound (e n w : ℕ) (_he : Even e) (hew : e ≤ 2 * w) (hw : 2 ^ w ≤ 2 * n) :
    (2 : ℝ) ^ ((e : ℝ) / 2 - 1) ≤ (n : ℝ) := by
  have h1 : (e : ℝ) / 2 ≤ (w : ℝ) := by
    have : (e : ℝ) ≤ 2 * (w : ℝ) := by exact_mod_cast hew
    linarith
  have h2 : (2 : ℝ) ^ ((e : ℝ) / 2 - 1) ≤ (2 : ℝ) ^ ((w : ℝ) - 1) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h3 : (2 : ℝ) ^ ((w : ℝ) - 1) = (2 : ℝ) ^ w / 2 := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_natCast, Real.rpow_one]
  have h4 : (2 : ℝ) ^ w ≤ 2 * (n : ℝ) := by exact_mod_cast hw
  rw [h3] at h2
  linarith

end CFSG.LocalAnalysis.RankThreeUC.Section5.WidthArithmetic
