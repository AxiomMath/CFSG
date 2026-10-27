module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModel
public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSix

open Matrix QuadraticMap CatalogueBOrthogonalFourNonsplit
open CFSG.ClassicalGroups.Orthogonal

universe u

variable {K : Type u} [Field K]

@[expose] def sixPolarGram (delta : K) : Matrix (Fin 6) (Fin 6) K :=
  !![0, 1, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 0;
     0, 0, -2, 0, 0, 0;
     0, 0, 0, 2 * delta, 0, 0;
     0, 0, 0, 0, 0, delta;
     0, 0, 0, 0, delta, 0]

theorem sixPolarGram_det (delta : K) : (sixPolarGram delta).det = -4 * delta ^ 3 := by
  simp [sixPolarGram, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Matrix.submatrix, Fin.succAbove]
  ring

theorem sixPolarGram_form (delta : K) [Fact (¬ IsSquare delta)] (h2 : (2 : K) ≠ 0)
    (x y : Fin 6 → K) :
    (sixForm delta).polarBilin (sixCoordinates delta h2 x) (sixCoordinates delta h2 y) =
      Matrix.toBilin' (sixPolarGram delta) x y := by
  rw [sixForm_polar, Matrix.toBilin'_apply]
  simp [sixCoordinates, sixCoordinateMatrix, skewMatrix, sixPolarGram,
    Fin.sum_univ_succ]
  ring

@[expose] def threeHyperbolicGram (K : Type*) [Field K] : Matrix (Fin 6) (Fin 6) K :=
  !![0, 1, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 0]

theorem threeHyperbolicGram_det : (threeHyperbolicGram K).det = -1 := by
  simp [threeHyperbolicGram, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Matrix.submatrix, Fin.succAbove]

private def hyperbolicSixFamily {V : Type*} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (P₁ P₂ P₃ : HypPair Q) : Fin 6 → V :=
  ![P₁.e, P₁.f, P₂.e, P₂.f, P₃.e, P₃.f]

private theorem hyperbolicSixFamily_polar {V : Type*} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (P₁ P₂ P₃ : HypPair Q)
    (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃) (i j : Fin 6) :
    polar Q (hyperbolicSixFamily P₁ P₂ P₃ i) (hyperbolicSixFamily P₁ P₂ P₃ j) =
      threeHyperbolicGram K i j := by
  fin_cases i <;> fin_cases j
  · change polar Q P₁.e P₁.e = 0
    exact P₁.polar_ee
  · change polar Q P₁.e P₁.f = 1
    exact P₁.polar_ef
  · change polar Q P₁.e P₂.e = 0
    exact h₁₂.ee
  · change polar Q P₁.e P₂.f = 0
    exact h₁₂.ef
  · change polar Q P₁.e P₃.e = 0
    exact h₁₃.ee
  · change polar Q P₁.e P₃.f = 0
    exact h₁₃.ef
  · change polar Q P₁.f P₁.e = 1
    exact P₁.polar_fe
  · change polar Q P₁.f P₁.f = 0
    exact P₁.polar_ff
  · change polar Q P₁.f P₂.e = 0
    exact h₁₂.fe
  · change polar Q P₁.f P₂.f = 0
    exact h₁₂.ff
  · change polar Q P₁.f P₃.e = 0
    exact h₁₃.fe
  · change polar Q P₁.f P₃.f = 0
    exact h₁₃.ff
  · change polar Q P₂.e P₁.e = 0
    exact h₁₂.symm.ee
  · change polar Q P₂.e P₁.f = 0
    exact h₁₂.symm.ef
  · change polar Q P₂.e P₂.e = 0
    exact P₂.polar_ee
  · change polar Q P₂.e P₂.f = 1
    exact P₂.polar_ef
  · change polar Q P₂.e P₃.e = 0
    exact h₂₃.ee
  · change polar Q P₂.e P₃.f = 0
    exact h₂₃.ef
  · change polar Q P₂.f P₁.e = 0
    exact h₁₂.symm.fe
  · change polar Q P₂.f P₁.f = 0
    exact h₁₂.symm.ff
  · change polar Q P₂.f P₂.e = 1
    exact P₂.polar_fe
  · change polar Q P₂.f P₂.f = 0
    exact P₂.polar_ff
  · change polar Q P₂.f P₃.e = 0
    exact h₂₃.fe
  · change polar Q P₂.f P₃.f = 0
    exact h₂₃.ff
  · change polar Q P₃.e P₁.e = 0
    exact h₁₃.symm.ee
  · change polar Q P₃.e P₁.f = 0
    exact h₁₃.symm.ef
  · change polar Q P₃.e P₂.e = 0
    exact h₂₃.symm.ee
  · change polar Q P₃.e P₂.f = 0
    exact h₂₃.symm.ef
  · change polar Q P₃.e P₃.e = 0
    exact P₃.polar_ee
  · change polar Q P₃.e P₃.f = 1
    exact P₃.polar_ef
  · change polar Q P₃.f P₁.e = 0
    exact h₁₃.symm.fe
  · change polar Q P₃.f P₁.f = 0
    exact h₁₃.symm.ff
  · change polar Q P₃.f P₂.e = 0
    exact h₂₃.symm.fe
  · change polar Q P₃.f P₂.f = 0
    exact h₂₃.symm.ff
  · change polar Q P₃.f P₃.e = 1
    exact P₃.polar_fe
  · change polar Q P₃.f P₃.f = 0
    exact P₃.polar_ff

private def coordinateMatrix {V : Type*} [AddCommGroup V] [Module K V]
    (e : (Fin 6 → K) ≃ₗ[K] V) (v : Fin 6 → V) : Matrix (Fin 6) (Fin 6) K :=
  fun i j => e.symm (v j) i

private theorem gramCongruence_entry (G M : Matrix (Fin 6) (Fin 6) K) (i j : Fin 6) :
    (M.transpose * G * M) i j = Matrix.toBilin' G (fun k => M k i) (fun k => M k j) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.toBilin'_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]

private theorem coordinateGram_congruence {V : Type*} [AddCommGroup V] [Module K V]
    (e : (Fin 6 → K) ≃ₗ[K] V) (B : LinearMap.BilinForm K V)
    (G : Matrix (Fin 6) (Fin 6) K)
    (hG : ∀ x y, B (e x) (e y) = Matrix.toBilin' G x y) (v : Fin 6 → V) :
    (coordinateMatrix e v).transpose * G * coordinateMatrix e v =
      LinearMap.BilinForm.toMatrixAux v B := by
  apply Matrix.ext
  intro i j
  rw [gramCongruence_entry, LinearMap.BilinForm.toMatrixAux_apply]
  change Matrix.toBilin' G (e.symm (v i)) (e.symm (v j)) = B (v i) (v j)
  rw [← hG, e.apply_symm_apply, e.apply_symm_apply]

private theorem six_hyperbolic_congruence (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) (P₁ P₂ P₃ : HypPair (sixForm delta))
    (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃) :
    let M : Matrix (Fin 6) (Fin 6) K :=
      fun i j => (sixCoordinates delta h2).symm (hyperbolicSixFamily P₁ P₂ P₃ j) i
    M.transpose * sixPolarGram delta * M = threeHyperbolicGram K := by
  change (coordinateMatrix (sixCoordinates delta h2) (hyperbolicSixFamily P₁ P₂ P₃)).transpose *
    sixPolarGram delta * coordinateMatrix (sixCoordinates delta h2) (hyperbolicSixFamily P₁ P₂ P₃) = _
  rw [coordinateGram_congruence (sixCoordinates delta h2) (sixForm delta).polarBilin
    (sixPolarGram delta) (sixPolarGram_form delta h2)]
  apply Matrix.ext
  intro i j
  exact hyperbolicSixFamily_polar P₁ P₂ P₃ h₁₂ h₁₃ h₂₃ i j

theorem six_no_three_hyperbolic_pairs (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) (P₁ P₂ P₃ : HypPair (sixForm delta))
    (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃) : False := by
  let M : Matrix (Fin 6) (Fin 6) K :=
    fun i j => (sixCoordinates delta h2).symm (hyperbolicSixFamily P₁ P₂ P₃ j) i
  have hd := congrArg Matrix.det (six_hyperbolic_congruence delta h2 P₁ P₂ P₃ h₁₂ h₁₃ h₂₃)
  change (M.transpose * sixPolarGram delta * M).det = (threeHyperbolicGram K).det at hd
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    sixPolarGram_det, threeHyperbolicGram_det] at hd
  have he : 4 * delta ^ 3 * M.det ^ 2 = 1 := by linear_combination -hd
  have hn : ¬ IsSquare delta := Fact.out
  apply hn
  refine ⟨2 * delta ^ 2 * M.det, ?_⟩
  linear_combination -delta * he

theorem six_no_totally_singular_three (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) (T : Submodule K (sixSubmodule delta))
    (hT : 3 ≤ Module.finrank K T) (hTQ : ∀ x ∈ T, sixForm delta x = 0) : False := by
  let : FiniteDimensional K (sixSubmodule delta) := Module.Finite.equiv (sixCoordinates delta h2)
  obtain ⟨P₁, P₂, P₃, h₁₂, h₁₃, h₂₃⟩ :=
    exists_three_hypPairs (sixForm_nondegenerate delta h2) hT hTQ
  exact six_no_three_hyperbolic_pairs delta h2 P₁ P₂ P₃ h₁₂ h₁₃ h₂₃

theorem six_totally_singular_finrank_le_two (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) (T : Submodule K (sixSubmodule delta))
    (hTQ : ∀ x ∈ T, sixForm delta x = 0) : Module.finrank K T ≤ 2 := by
  by_contra h
  exact six_no_totally_singular_three delta h2 T (by omega) hTQ

end CFSG.ComponentClassification.CatalogueBOrthogonalSix
