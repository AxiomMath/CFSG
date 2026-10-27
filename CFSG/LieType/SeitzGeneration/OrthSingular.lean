module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticNormalForms

public section

namespace CFSG.LieType.SeitzGeneration

open Polynomial Module QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem exists_singular_of_three_le_odd (h2 : (2 : K) ≠ 0) {S : Submodule K V}
    (h3 : 3 ≤ finrank K S) : ∃ x ∈ S, x ≠ 0 ∧ Q x = 0 := by
  classical
  obtain ⟨⟨e₁, he₁S⟩, he₁0'⟩ :=
    Module.finrank_pos_iff_exists_ne_zero.mp (by omega : 0 < finrank K S)
  have he₁0 : e₁ ≠ 0 := fun h => he₁0' (Subtype.ext h)
  by_cases hQ1 : Q e₁ = 0
  · exact ⟨e₁, he₁S, he₁0, hQ1⟩
  obtain ⟨e₂, he₂S, he₂0, h12, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.exists_mem_orth_two Q h3 e₁ e₁
  by_cases hQ2 : Q e₂ = 0
  · exact ⟨e₂, he₂S, he₂0, hQ2⟩
  obtain ⟨e₃, he₃S, he₃0, h13, h23⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.exists_mem_orth_two Q h3 e₁ e₂
  by_cases hQ3 : Q e₃ = 0
  · exact ⟨e₃, he₃S, he₃0, hQ3⟩
  have : Fintype K := Fintype.ofFinite K
  have hodd : Fintype.card K % 2 = 1 := by
    have hchar : ringChar K ≠ 2 := fun h => h2 (by
      have := (ringChar.spec K 2).mpr (by rw [h])
      exact_mod_cast this)
    exact FiniteField.odd_card_of_char_ne_two hchar
  have hdeg1 : degree (C (Q e₂) * X ^ 2 + C (Q e₃) : K[X]) = 2 := by
    have h1 : degree (C (Q e₂) * X ^ 2 : K[X]) = 2 := by
      simpa using degree_C_mul_X_pow 2 hQ2
    rw [degree_add_C (by rw [h1]; norm_num), h1]
  obtain ⟨x, y, hxy⟩ := FiniteField.exists_root_sum_quadratic
    (f := C (Q e₁) * X ^ 2) (g := C (Q e₂) * X ^ 2 + C (Q e₃))
    (by simpa using degree_C_mul_X_pow 2 hQ1) hdeg1 hodd
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X] at hxy
  refine ⟨x • e₁ + y • e₂ + e₃, S.add_mem (S.add_mem (S.smul_mem _ he₁S) (S.smul_mem _ he₂S))
    he₃S, fun h0 => ?_, ?_⟩
  · have h1 := congrArg (fun v => polar Q v e₃) h0
    simp only [polar_add_left, polar_smul_left_eq, polar_zero_left] at h1
    rw [h13, h23, polar_self] at h1
    simp only [mul_zero, zero_add, nsmul_eq_mul] at h1
    exact mul_ne_zero h2 hQ3 (by simpa using h1)
  · have hp12 : polar Q (x • e₁) (y • e₂) = 0 := by
      rw [polar_smul_left_eq, polar_smul_right_eq, h12]
      ring
    have hp3 : polar Q (x • e₁ + y • e₂) e₃ = 0 := by
      rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, h13, h23]
      ring
    rw [QuadraticMap.map_add Q (x • e₁ + y • e₂) e₃, QuadraticMap.map_add Q (x • e₁) (y • e₂),
      map_smul_eq_sq, map_smul_eq_sq, hp12, hp3]
    linear_combination hxy

theorem exists_singular_of_three_le_general {S : Submodule K V} (hS : PolarNondegOn Q S)
    (h3 : 3 ≤ finrank K S) : ∃ x ∈ S, x ≠ 0 ∧ Q x = 0 := by
  by_cases h2 : (2 : K) = 0
  · have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    exact CFSG.ComponentClassification.UnbalancedCatalog.exists_singular_of_three_le hS h3
  · exact exists_singular_of_three_le_odd h2 h3

end CFSG.LieType.SeitzGeneration
