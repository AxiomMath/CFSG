module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeArithmeticDivisibility
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeArithmeticUniqueness

public section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeArithmetic

theorem fixed_parameter_involution_degree_arithmetic :
    (∀ q : ℤ, 4 ≤ q →
      degreeF 1 q < degreeF 2 q ∧ degreeF 2 q < degreeF 3 q ∧
        degreeG 1 q < degreeG 2 q ∧ degreeG 2 q < degreeG 3 q ∧
        (∀ i j : ℕ, 1 ≤ i → i ≤ 3 → 1 ≤ j → j ≤ 3 →
          degreeG j q < degreeF i (q ^ 2)) ∧
        degreeG 1 q = (q : ℚ) ^ 2 + 1 ∧
        degreeG 3 q = (q : ℚ) ^ 6 - 2 * (q : ℚ) ^ 5 + 2 * (q : ℚ) ^ 4 + 1 ∧
        (¬ ∃ m : ℤ, degreeG 2 q = (m : ℚ)) ∧
        (∀ m : ℤ, degreeG 3 q = (m : ℚ) → ¬ q ^ 2 - 1 ∣ m - 2)) ∧
      (∀ b : ℤ, 4 ≤ b → (∃ f : ℕ, b = 2 ^ f) → ∀ n : ℚ,
        {r : DegreeRepresentation | representsDegree b n r}.Subsingleton) := by
  refine ⟨?_, fixed_parameter_degree_unique⟩
  intro q hq
  obtain ⟨hf12, hf23, hg12, hg23⟩ := degree_exponent_chains q hq
  refine ⟨hf12, hf23, hg12, hg23, ?_, degreeG_one q hq,
    degreeG_three q hq, degreeG_two_not_integer q hq, ?_⟩
  · intro i j hi _ _ hj
    exact degree_square_parameter_separation q hq i j hi hj
  · intro m hm
    have heq : degreeGThreeInteger q = m := by
      apply Int.cast_injective (α := ℚ)
      exact (degreeG_three_eq_integer q hq).symm.trans hm
    rw [← heq]
    exact degreeG_three_minus_two_not_dvd q hq

end CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeArithmetic
