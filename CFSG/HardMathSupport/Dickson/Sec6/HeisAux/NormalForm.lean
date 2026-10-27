module

public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.Heis

open Matrix Polynomial

variable {F : Type*} [Field F]

theorem exists_eigenvector_of_cube_one (ζ : F) (hζ : ζ ^ 2 + ζ + 1 = 0)
    (M0 : Matrix (Fin 3) (Fin 3) F) (hM0 : M0 ^ 3 = 1) :
    ∃ θ : F, (θ = 1 ∨ θ = ζ ∨ θ = ζ ^ 2) ∧ ∃ v : Fin 3 → F, v ≠ 0 ∧ M0 *ᵥ v = θ • v := by
  have hζ3 : ζ ^ 3 = 1 := by linear_combination (ζ - 1) * hζ
  have hpoly : ((X - C 1) * (X - C ζ) * (X - C (ζ ^ 2)) : F[X]) = X ^ 3 - C 1 := by
    have e1 : (C (1 + ζ + ζ ^ 2) : F[X]) = 0 := by
      rw [show 1 + ζ + ζ ^ 2 = 0 by linear_combination hζ, map_zero]
    have e2 : (C (ζ + ζ ^ 2 + ζ ^ 3) : F[X]) = 0 := by
      rw [show ζ + ζ ^ 2 + ζ ^ 3 = 0 by linear_combination ζ * hζ, map_zero]
    have e3 : (C (ζ ^ 3) : F[X]) = C 1 := by rw [hζ3]
    simp only [map_add, map_pow] at e1 e2 e3
    calc ((X - C 1) * (X - C ζ) * (X - C (ζ ^ 2)) : F[X])
        = X ^ 3 - (C 1 + C ζ + C ζ ^ 2) * X ^ 2 + (C ζ + C ζ ^ 2 + C ζ ^ 3) * X - C ζ ^ 3 := by
          simp only [map_one, map_pow]; ring
      _ = X ^ 3 - C 1 := by rw [e1, e2, e3]; simp
  have hmat := congrArg (Polynomial.aeval M0) hpoly
  simp only [map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, map_pow, hM0, map_one] at hmat
  rw [sub_self] at hmat
  have key : ∀ c : F, (M0 - algebraMap F (Matrix (Fin 3) (Fin 3) F) c).det = 0 →
      ∃ v : Fin 3 → F, v ≠ 0 ∧ M0 *ᵥ v = c • v := by
    intro c h
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    refine ⟨v, hv0, ?_⟩
    rw [Matrix.sub_mulVec, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec,
      sub_eq_zero] at hv
    exact hv
  have hdet : (M0 - algebraMap F (Matrix (Fin 3) (Fin 3) F) 1).det *
      (M0 - algebraMap F (Matrix (Fin 3) (Fin 3) F) ζ).det *
      (M0 - algebraMap F (Matrix (Fin 3) (Fin 3) F) (ζ ^ 2)).det = 0 := by
    rw [← Matrix.det_mul, ← Matrix.det_mul]
    simp only [map_one, map_pow] at hmat ⊢
    rw [hmat, Matrix.det_zero]
  rcases mul_eq_zero.1 hdet with h | h
  · rcases mul_eq_zero.1 h with h | h
    · obtain ⟨v, hv0, hv⟩ := key 1 h
      exact ⟨1, Or.inl rfl, v, hv0, hv⟩
    · obtain ⟨v, hv0, hv⟩ := key ζ h
      exact ⟨ζ, Or.inr (Or.inl rfl), v, hv0, hv⟩
  · obtain ⟨v, hv0, hv⟩ := key (ζ ^ 2) h
    exact ⟨ζ ^ 2, Or.inr (Or.inr rfl), v, hv0, hv⟩

theorem normal_form (ζ μ : F) (hζ : ζ ^ 2 + ζ + 1 = 0) (hζ1 : ζ ≠ 1) (hμ : μ ≠ 0)
    (M0 M : Matrix (Fin 3) (Fin 3) F) (hM0 : M0 ^ 3 = 1)
    (hM3 : M ^ 3 = μ • (1 : Matrix (Fin 3) (Fin 3) F)) (hcomm : M0 * M = ζ • (M * M0)) :
    ∃ (B : Matrix (Fin 3) (Fin 3) F) (θ : F), IsUnit B ∧ θ ≠ 0 ∧
      M0 * B = B * Matrix.diagonal ![θ, θ * ζ, θ * ζ ^ 2] ∧
      M * B = B * !![0, 0, μ; 1, 0, 0; 0, 1, 0] := by
  obtain ⟨θ, hθ, v, hv0, hv⟩ := exists_eigenvector_of_cube_one ζ hζ M0 hM0
  have hζ3 : ζ ^ 3 = 1 := by linear_combination (ζ - 1) * hζ
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    simp at hζ
  have hθ0 : θ ≠ 0 := by rcases hθ with rfl | rfl | rfl <;> simp [hζ0]
  have hζ21 : ζ ^ 2 ≠ 1 := fun h => hζ1 (by
    have : ζ ^ 3 = ζ := by rw [pow_succ, h, one_mul]
    rw [← this, hζ3])
  have hζζ2 : ζ ≠ ζ ^ 2 := fun h => by
    have : ζ * (1 - ζ) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h' | h'
    · exact hζ0 h'
    · exact hζ1 (by linear_combination -h')
  set w2 : Fin 3 → F := M *ᵥ v with hw2
  set w3 : Fin 3 → F := M *ᵥ w2 with hw3
  have hMMM : M * M * M = M ^ 3 := by rw [pow_succ, pow_two]
  have hM3v : M *ᵥ w3 = μ • v := by
    rw [hw3, hw2, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hMMM, hM3, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  have hw2ne : w2 ≠ 0 := fun h => hv0 (by
    have h1 : M *ᵥ w3 = 0 := by rw [hw3, h, Matrix.mulVec_zero, Matrix.mulVec_zero]
    rw [hM3v] at h1
    exact (smul_eq_zero.1 h1).resolve_left hμ)
  have hw3ne : w3 ≠ 0 := fun h => hv0 (by
    have h1 : M *ᵥ w3 = 0 := by rw [h, Matrix.mulVec_zero]
    rw [hM3v] at h1
    exact (smul_eq_zero.1 h1).resolve_left hμ)
  have hcv : ∀ x : Fin 3 → F, M0 *ᵥ (M *ᵥ x) = ζ • (M *ᵥ (M0 *ᵥ x)) := fun x => by
    rw [Matrix.mulVec_mulVec, hcomm, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]
  have h2 : M0 *ᵥ w2 = (θ * ζ) • w2 := by
    rw [hw2, hcv, hv, Matrix.mulVec_smul, smul_smul, mul_comm]
  have h3 : M0 *ᵥ w3 = (θ * ζ ^ 2) • w3 := by
    rw [hw3, hcv, h2, Matrix.mulVec_smul, smul_smul]
    congr 1
    ring
  have h01 : θ ≠ θ * ζ := fun h => hζ1 (mul_left_cancel₀ hθ0 (by rw [mul_one]; exact h.symm))
  have h02 : θ ≠ θ * ζ ^ 2 := fun h => hζ21 (mul_left_cancel₀ hθ0 (by rw [mul_one]; exact h.symm))
  have h12 : θ * ζ ≠ θ * ζ ^ 2 := fun h => hζζ2 (mul_left_cancel₀ hθ0 h)
  have hinj : Function.Injective (![θ, θ * ζ, θ * ζ ^ 2] : Fin 3 → F) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; simp_all)
  have hli : LinearIndependent F (![v, w2, w3] : Fin 3 → Fin 3 → F) := by
    refine Module.End.eigenvectors_linearIndependent' (Matrix.toLin' M0) ![θ, θ * ζ, θ * ζ ^ 2]
      hinj ![v, w2, w3] ?_
    intro i
    refine ⟨Module.End.mem_eigenspace_iff.2 ?_, ?_⟩
    · fin_cases i
      · simpa [Matrix.toLin'_apply] using hv
      · simpa [Matrix.toLin'_apply] using h2
      · simpa [Matrix.toLin'_apply] using h3
    · fin_cases i
      · simpa using hv0
      · simpa using hw2ne
      · simpa using hw3ne
  set B : Matrix (Fin 3) (Fin 3) F := Matrix.of fun i j => (![v, w2, w3] j) i with hB
  have hBcol : B.col = ![v, w2, w3] := by
    funext j
    ext i
    rfl
  have hcol : ∀ (X : Matrix (Fin 3) (Fin 3) F) (i j : Fin 3),
      (X * B) i j = (X *ᵥ (![v, w2, w3] j)) i := fun X i j => rfl
  refine ⟨B, θ, Matrix.linearIndependent_cols_iff_isUnit.1 (by rw [hBcol]; exact hli), hθ0, ?_, ?_⟩
  · ext i j
    rw [hcol, Matrix.mul_diagonal]
    fin_cases j
    · show (M0 *ᵥ v) i = v i * θ
      rw [hv]
      simp [mul_comm]
    · show (M0 *ᵥ w2) i = w2 i * (θ * ζ)
      rw [h2]
      simp [mul_comm]
    · show (M0 *ᵥ w3) i = w3 i * (θ * ζ ^ 2)
      rw [h3]
      simp [mul_comm]
  · ext i j
    rw [hcol]
    fin_cases j
    · show (M *ᵥ v) i = _
      simp [hB, Matrix.mul_apply, Fin.sum_univ_three, hw2]
    · show (M *ᵥ w2) i = _
      simp [hB, Matrix.mul_apply, Fin.sum_univ_three, hw3]
    · show (M *ᵥ w3) i = _
      rw [hM3v]
      simp [hB, Matrix.mul_apply, Fin.sum_univ_three, mul_comm]

end CFSG.HardMathSupport.Dickson.Sec6.Heis
