module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionTwoAdicBasic

public section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionTwoAdic

theorem linear_involution_count (q n : ℤ) (hq : 2 ≤ q) (_hn : 1 ≤ n)
    (hcount : (n : ℚ) - 1 = (q : ℚ) *
      (((q : ℚ) + 1) * ((q : ℚ) - 1) / ((q : ℚ) + 1) + 1)) :
    n - 1 = q ^ 2 := by
  have hden : (q : ℚ) + 1 ≠ 0 := by
    have hqQ : (2 : ℚ) ≤ q := by exact_mod_cast hq
    linarith
  rw [mul_div_cancel_left₀ ((q : ℚ) - 1) hden] at hcount
  have heq : (n : ℚ) - 1 = (q : ℚ) ^ 2 := by nlinarith [hcount]
  exact_mod_cast heq

end CFSG.ProperTwoGeneratedCore.LocalCriterionTwoAdic
