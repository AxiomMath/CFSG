module

public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerPSLComplex

public section

namespace CFSG.ClassicalInvolution.Q3

open Matrix
open scoped MatrixGroups

section Blocks

variable {F : Type} [Field F] {m : ℕ}

@[expose] def gReal (A : Matrix (Fin m) (Fin m) (GaussField F)) : Matrix (Fin m) (Fin m) F :=
  A.map QuadraticAlgebra.re

@[expose] def gImag (A : Matrix (Fin m) (Fin m) (GaussField F)) : Matrix (Fin m) (Fin m) F :=
  A.map QuadraticAlgebra.im

theorem re_sum {ι : Type} (s : Finset ι) (x : ι → GaussField F) :
    (∑ j ∈ s, x j).re = ∑ j ∈ s, (x j).re :=
  map_sum (QuadraticAlgebra.reₗ (R := F) (a := (-1 : F)) (b := 0)) x s

theorem im_sum {ι : Type} (s : Finset ι) (x : ι → GaussField F) :
    (∑ j ∈ s, x j).im = ∑ j ∈ s, (x j).im :=
  map_sum (QuadraticAlgebra.imₗ (R := F) (a := (-1 : F)) (b := 0)) x s

theorem gReal_mul (A B : Matrix (Fin m) (Fin m) (GaussField F)) :
    gReal (A * B) = gReal A * gReal B - gImag A * gImag B := by
  ext k l
  simp only [gReal, gImag, Matrix.mul_apply, Matrix.map_apply, Matrix.sub_apply, re_sum,
    QuadraticAlgebra.re_mul, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem gImag_mul (A B : Matrix (Fin m) (Fin m) (GaussField F)) :
    gImag (A * B) = gReal A * gImag B + gImag A * gReal B := by
  ext k l
  simp only [gReal, gImag, Matrix.mul_apply, Matrix.map_apply, Matrix.add_apply, im_sum,
    QuadraticAlgebra.im_mul, ← Finset.sum_add_distrib]
  simp

theorem gReal_one : gReal (1 : Matrix (Fin m) (Fin m) (GaussField F)) = 1 := by
  ext k l
  by_cases h : k = l
  · subst h
    simp [gReal, QuadraticAlgebra.re_one]
  · simp [gReal, h]

theorem gImag_one : gImag (1 : Matrix (Fin m) (Fin m) (GaussField F)) = 0 := by
  ext k l
  by_cases h : k = l
  · subst h
    simp [gImag, QuadraticAlgebra.im_one]
  · simp [gImag, h]

theorem gReal_add (A B : Matrix (Fin m) (Fin m) (GaussField F)) :
    gReal (A + B) = gReal A + gReal B := by
  ext k l
  simp [gReal]

theorem gImag_add (A B : Matrix (Fin m) (Fin m) (GaussField F)) :
    gImag (A + B) = gImag A + gImag B := by
  ext k l
  simp [gImag]

@[expose] def gaussBlocks (m : ℕ) :
    Matrix (Fin m) (Fin m) (GaussField F) →+* Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F where
  toFun A := Matrix.fromBlocks (gReal A) (-gImag A) (gImag A) (gReal A)
  map_one' := by
    rw [gReal_one, gImag_one, neg_zero, Matrix.fromBlocks_one]
  map_mul' A B := by
    rw [Matrix.fromBlocks_multiply, gReal_mul, gImag_mul]
    congr 1 <;> first | noncomm_ring | abel
  map_zero' := by
    have h1 : gReal (0 : Matrix (Fin m) (Fin m) (GaussField F)) = 0 := by ext; simp [gReal]
    have h2 : gImag (0 : Matrix (Fin m) (Fin m) (GaussField F)) = 0 := by ext; simp [gImag]
    rw [h1, h2, neg_zero, Matrix.fromBlocks_zero]
  map_add' A B := by
    rw [gReal_add, gImag_add, Matrix.fromBlocks_add]
    congr 1
    rw [neg_add]

theorem gaussBlocks_apply (A : Matrix (Fin m) (Fin m) (GaussField F)) :
    gaussBlocks m A = Matrix.fromBlocks (gReal A) (-gImag A) (gImag A) (gReal A) := rfl

theorem gaussBlocks_injective : Function.Injective (gaussBlocks (F := F) m) := by
  intro A B h
  rw [gaussBlocks_apply, gaussBlocks_apply] at h
  have h1 := congrArg Matrix.toBlocks₁₁ h
  have h2 := congrArg Matrix.toBlocks₂₁ h
  simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₂₁] at h1 h2
  refine Matrix.ext fun k l => ?_
  exact QuadraticAlgebra.ext (congrFun (congrFun h1 k) l) (congrFun (congrFun h2 k) l)

theorem gReal_scalar (c : GaussField F) :
    gReal (Matrix.scalar (Fin m) c) = Matrix.scalar (Fin m) c.re := by
  ext k l
  by_cases h : k = l
  · subst h
    simp [gReal]
  · simp [gReal, h]

theorem gImag_scalar (c : GaussField F) :
    gImag (Matrix.scalar (Fin m) c) = Matrix.scalar (Fin m) c.im := by
  ext k l
  by_cases h : k = l
  · subst h
    simp [gImag]
  · simp [gImag, h]

theorem diagonal_neg_one' {ι : Type} [Fintype ι] [DecidableEq ι] :
    (Matrix.diagonal fun _ : ι => (-1 : F)) = -1 := by
  ext i j
  by_cases h : i = j
  · subst h
    simp
  · simp [h]

theorem gaussBlocks_scalar_omega :
    gaussBlocks m (Matrix.scalar (Fin m) (QuadraticAlgebra.omega : GaussField F)) =
      Matrix.fromBlocks 0 (-1) 1 0 := by
  rw [gaussBlocks_apply, gReal_scalar, gImag_scalar]
  simp [Matrix.scalar_apply, QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega]

theorem gaussBlocks_scalar_neg_omega :
    gaussBlocks m (Matrix.scalar (Fin m) (-(QuadraticAlgebra.omega : GaussField F))) =
      Matrix.fromBlocks 0 1 (-1) 0 := by
  rw [gaussBlocks_apply, gReal_scalar, gImag_scalar]
  simp [Matrix.scalar_apply, QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega,
    diagonal_neg_one']

theorem exists_gaussBlocks_of_commute {X : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F}
    (hX : X * Matrix.fromBlocks 0 (-1) 1 0 = Matrix.fromBlocks 0 (-1) 1 0 * X) :
    ∃ A : Matrix (Fin m) (Fin m) (GaussField F), gaussBlocks m A = X := by
  rw [← Matrix.fromBlocks_toBlocks X] at hX
  simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_one, Matrix.one_mul] at hX
  have h12 := congrArg Matrix.toBlocks₁₁ hX
  have h22 := congrArg Matrix.toBlocks₁₂ hX
  simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂] at h12 h22
  refine ⟨Matrix.of fun k l => (⟨X.toBlocks₁₁ k l, X.toBlocks₂₁ k l⟩ : GaussField F), ?_⟩
  rw [gaussBlocks_apply]
  have hr : gReal (Matrix.of fun k l => (⟨X.toBlocks₁₁ k l, X.toBlocks₂₁ k l⟩ : GaussField F)) =
      X.toBlocks₁₁ := by ext; simp [gReal]
  have hi : gImag (Matrix.of fun k l => (⟨X.toBlocks₁₁ k l, X.toBlocks₂₁ k l⟩ : GaussField F)) =
      X.toBlocks₂₁ := by ext; simp [gImag]
  rw [hr, hi]
  have h22' : X.toBlocks₂₂ = X.toBlocks₁₁ := (neg_inj.mp h22).symm
  conv_rhs => rw [← Matrix.fromBlocks_toBlocks X, h12, h22']

theorem omega_mul_neg_omega :
    (QuadraticAlgebra.omega : GaussField F) * -QuadraticAlgebra.omega = 1 := by
  apply QuadraticAlgebra.ext <;>
    simp [QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega, QuadraticAlgebra.re_one,
      QuadraticAlgebra.im_one]

section Unitary

open CFSG.LieType.Universal.Unitary

variable [Fact (¬ IsSquare (-1 : F))] (σ : GaussField F ≃+* GaussField F)

theorem gReal_conjTr (hσ : ∀ z : GaussField F, σ z = ⟨z.re, -z.im⟩)
    (A : Matrix (Fin m) (Fin m) (GaussField F)) : gReal (conjTr σ A) = (gReal A)ᵀ := by
  ext k l
  simp [gReal, conjTr, hσ]

theorem gImag_conjTr (hσ : ∀ z : GaussField F, σ z = ⟨z.re, -z.im⟩)
    (A : Matrix (Fin m) (Fin m) (GaussField F)) : gImag (conjTr σ A) = -(gImag A)ᵀ := by
  ext k l
  simp [gImag, conjTr, hσ]

theorem gaussBlocks_transpose (hσ : ∀ z : GaussField F, σ z = ⟨z.re, -z.im⟩)
    (A : Matrix (Fin m) (Fin m) (GaussField F)) :
    (gaussBlocks m A)ᵀ = gaussBlocks m (conjTr σ A) := by
  rw [gaussBlocks_apply, gaussBlocks_apply, Matrix.fromBlocks_transpose, gReal_conjTr σ hσ,
    gImag_conjTr σ hσ, neg_neg, Matrix.transpose_neg]

theorem symplectic_gaussBlocks_iff (hσ : ∀ z : GaussField F, σ z = ⟨z.re, -z.im⟩)
    (A : Matrix (Fin m) (Fin m) (GaussField F)) :
    (gaussBlocks m A)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * gaussBlocks m A =
      Matrix.fromBlocks 0 1 (-1) 0 ↔ conjTr σ A * A = 1 := by
  set W : Matrix (Fin m) (Fin m) (GaussField F) :=
    Matrix.scalar (Fin m) (-(QuadraticAlgebra.omega : GaussField F)) with hW
  have hWc : ∀ X : Matrix (Fin m) (Fin m) (GaussField F), W * X = X * W := fun X =>
    (Matrix.scalar_commute _ (fun r => Commute.all _ r) X).eq
  have hWW : (Matrix.scalar (Fin m) (QuadraticAlgebra.omega : GaussField F)) * W = 1 := by
    rw [hW, ← map_mul, omega_mul_neg_omega, map_one]
  rw [← gaussBlocks_scalar_neg_omega, ← hW, gaussBlocks_transpose σ hσ, ← map_mul, ← map_mul]
  constructor
  · intro h
    have h1 : conjTr σ A * W * A = W := gaussBlocks_injective h
    have h2 : W * (conjTr σ A * A) = W := by
      calc W * (conjTr σ A * A) = conjTr σ A * W * A := by
            rw [← Matrix.mul_assoc, hWc (conjTr σ A)]
        _ = W := h1
    calc conjTr σ A * A = (Matrix.scalar (Fin m) (QuadraticAlgebra.omega : GaussField F)) *
          (W * (conjTr σ A * A)) := by rw [← Matrix.mul_assoc, hWW, Matrix.one_mul]
      _ = 1 := by rw [h2, hWW]
  · intro h
    congr 1
    calc conjTr σ A * W * A = W * (conjTr σ A * A) := by
          rw [← hWc (conjTr σ A), Matrix.mul_assoc]
      _ = W := by rw [h, Matrix.mul_one]

end Unitary

end Blocks

end CFSG.ClassicalInvolution.Q3
