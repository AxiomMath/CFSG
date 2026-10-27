module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionTwoAdicLinear
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionTwoAdicSuzuki
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionTwoAdicUnitary

public section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionTwoAdic

theorem rank_one_involution_count_two_adic_obstructions :
    (∀ (q n : ℤ), 2 ≤ q → 1 ≤ n →
      (n : ℚ) - 1 = (q : ℚ) *
        (((q : ℚ) + 1) * ((q : ℚ) - 1) / ((q : ℚ) + 1) + 1) →
      n - 1 = q ^ 2) ∧
    (∀ (a : ℕ), 1 ≤ a → ∀ (eps n : ℤ), (eps = -1 ∨ eps = 1) → 1 ≤ n →
      (n : ℚ) - 1 = ((2 : ℚ) ^ (2 * a + 1)) ^ 2 *
        (((((2 : ℚ) ^ (2 * a + 1)) ^ 2 + 1) *
            ((2 : ℚ) ^ (2 * a + 1) - 1)) /
          ((2 : ℚ) ^ (2 * a + 1) + (eps : ℚ) * (2 : ℚ) ^ (a + 1) + 1) + 1) →
      let q : ℤ := 2 ^ (2 * a + 1)
      let r : ℤ := 2 ^ (a + 1)
      q ^ 2 * r ∣ n - 1 ∧ ¬ 2 * q ^ 2 * r ∣ n - 1 ∧ ¬ q ^ 3 ∣ n - 1) ∧
    (∀ (f : ℕ), 2 ≤ f → ∀ (n : ℤ), 1 ≤ n →
      (n : ℚ) - 1 = ((2 : ℚ) ^ f) ^ 3 *
        (((((2 : ℚ) ^ f) ^ 3 + 1) * ((2 : ℚ) ^ f - 1)) /
          (3 * ((2 : ℚ) ^ f + 1)) + 1) →
      let q : ℤ := 2 ^ f
      2 * q ^ 3 ∣ n - 1 ∧ ¬ 4 * q ^ 3 ∣ n - 1 ∧ ¬ q ^ 4 ∣ n - 1) := by
  exact ⟨linear_involution_count, suzuki_involution_count_two_part,
    unitary_involution_count_two_part⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionTwoAdic
