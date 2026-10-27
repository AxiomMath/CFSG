module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.ClassicalGroups.Symplectic.WedgeTwo

open Matrix

variable {R : Type*} [CommRing R]

abbrev wedgeJ (R : Type*) [CommRing R] : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R :=
  Matrix.fromBlocks 0 1 (-1) 0

@[expose] def wedgeFst : Fin 6 → Fin 2 ⊕ Fin 2 :=
  ![.inl 0, .inr 0, .inl 0, .inl 1, .inl 0, .inl 1]

@[expose] def wedgeSnd : Fin 6 → Fin 2 ⊕ Fin 2 :=
  ![.inl 1, .inr 1, .inr 1, .inr 0, .inr 0, .inr 1]

@[expose] def wedge2 (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) : Matrix (Fin 6) (Fin 6) R :=
  Matrix.of fun p q =>
    A (wedgeFst p) (wedgeFst q) * A (wedgeSnd p) (wedgeSnd q) -
      A (wedgeFst p) (wedgeSnd q) * A (wedgeSnd p) (wedgeFst q)

theorem wedge2_mul (A B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) :
    wedge2 (A * B) = wedge2 A * wedge2 B := by
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [wedge2, wedgeFst, wedgeSnd, Matrix.mul_apply, Fin.sum_univ_succ,
      Fintype.sum_sum_type] <;> ring

theorem wedge2_smul (c : R) (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) :
    wedge2 (c • A) = (c ^ 2) • wedge2 A := by
  ext p q
  simp only [wedge2, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Matrix.smul_of]
  ring

theorem wedge2_one : wedge2 (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) = 1 := by
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [wedge2, wedgeFst, wedgeSnd, Matrix.one_apply]

@[expose] def wedgeGram : Matrix (Fin 6) (Fin 6) R :=
  !![0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, -1; 0, 0, 0, 0, -1, 0]

private theorem fsf0 : (finSumFinEquiv.symm (0 : Fin 4) : Fin 2 ⊕ Fin 2) = .inl 0 := rfl
private theorem fsf1 : (finSumFinEquiv.symm (1 : Fin 4) : Fin 2 ⊕ Fin 2) = .inl 1 := rfl
private theorem fsf2 : (finSumFinEquiv.symm (2 : Fin 4) : Fin 2 ⊕ Fin 2) = .inr 0 := rfl
private theorem fsf3 : (finSumFinEquiv.symm (3 : Fin 4) : Fin 2 ⊕ Fin 2) = .inr 1 := rfl

theorem det_expand (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) :
    A.det =
      A (.inl 0) (.inl 0) * A (.inl 1) (.inl 1) * A (.inr 0) (.inr 0) * A (.inr 1) (.inr 1)
      - A (.inl 0) (.inl 0) * A (.inl 1) (.inl 1) * A (.inr 0) (.inr 1) * A (.inr 1) (.inr 0)
      - A (.inl 0) (.inl 0) * A (.inl 1) (.inr 0) * A (.inr 0) (.inl 1) * A (.inr 1) (.inr 1)
      + A (.inl 0) (.inl 0) * A (.inl 1) (.inr 0) * A (.inr 0) (.inr 1) * A (.inr 1) (.inl 1)
      + A (.inl 0) (.inl 0) * A (.inl 1) (.inr 1) * A (.inr 0) (.inl 1) * A (.inr 1) (.inr 0)
      - A (.inl 0) (.inl 0) * A (.inl 1) (.inr 1) * A (.inr 0) (.inr 0) * A (.inr 1) (.inl 1)
      - A (.inl 0) (.inl 1) * A (.inl 1) (.inl 0) * A (.inr 0) (.inr 0) * A (.inr 1) (.inr 1)
      + A (.inl 0) (.inl 1) * A (.inl 1) (.inl 0) * A (.inr 0) (.inr 1) * A (.inr 1) (.inr 0)
      + A (.inl 0) (.inl 1) * A (.inl 1) (.inr 0) * A (.inr 0) (.inl 0) * A (.inr 1) (.inr 1)
      - A (.inl 0) (.inl 1) * A (.inl 1) (.inr 0) * A (.inr 0) (.inr 1) * A (.inr 1) (.inl 0)
      - A (.inl 0) (.inl 1) * A (.inl 1) (.inr 1) * A (.inr 0) (.inl 0) * A (.inr 1) (.inr 0)
      + A (.inl 0) (.inl 1) * A (.inl 1) (.inr 1) * A (.inr 0) (.inr 0) * A (.inr 1) (.inl 0)
      + A (.inl 0) (.inr 0) * A (.inl 1) (.inl 0) * A (.inr 0) (.inl 1) * A (.inr 1) (.inr 1)
      - A (.inl 0) (.inr 0) * A (.inl 1) (.inl 0) * A (.inr 0) (.inr 1) * A (.inr 1) (.inl 1)
      - A (.inl 0) (.inr 0) * A (.inl 1) (.inl 1) * A (.inr 0) (.inl 0) * A (.inr 1) (.inr 1)
      + A (.inl 0) (.inr 0) * A (.inl 1) (.inl 1) * A (.inr 0) (.inr 1) * A (.inr 1) (.inl 0)
      + A (.inl 0) (.inr 0) * A (.inl 1) (.inr 1) * A (.inr 0) (.inl 0) * A (.inr 1) (.inl 1)
      - A (.inl 0) (.inr 0) * A (.inl 1) (.inr 1) * A (.inr 0) (.inl 1) * A (.inr 1) (.inl 0)
      - A (.inl 0) (.inr 1) * A (.inl 1) (.inl 0) * A (.inr 0) (.inl 1) * A (.inr 1) (.inr 0)
      + A (.inl 0) (.inr 1) * A (.inl 1) (.inl 0) * A (.inr 0) (.inr 0) * A (.inr 1) (.inl 1)
      + A (.inl 0) (.inr 1) * A (.inl 1) (.inl 1) * A (.inr 0) (.inl 0) * A (.inr 1) (.inr 0)
      - A (.inl 0) (.inr 1) * A (.inl 1) (.inl 1) * A (.inr 0) (.inr 0) * A (.inr 1) (.inl 0)
      - A (.inl 0) (.inr 1) * A (.inl 1) (.inr 0) * A (.inr 0) (.inl 0) * A (.inr 1) (.inl 1)
      + A (.inl 0) (.inr 1) * A (.inl 1) (.inr 0) * A (.inr 0) (.inl 1) * A (.inr 1) (.inl 0) := by
  rw [← Matrix.det_reindex_self (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4)]
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Fin.succAbove, fsf0, fsf1, fsf2, fsf3]
  ring

theorem transpose_mul_wedgeGram_mul_apply (M N : Matrix (Fin 6) (Fin 6) R) (k l : Fin 6) :
    (Mᵀ * wedgeGram * N : Matrix (Fin 6) (Fin 6) R) k l =
      M 0 k * N 1 l + M 1 k * N 0 l + M 2 k * N 3 l + M 3 k * N 2 l - M 4 k * N 5 l -
        M 5 k * N 4 l := by
  simp [wedgeGram, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

theorem wedge2_gram (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) :
    (wedge2 A)ᵀ * wedgeGram * wedge2 A = A.det • wedgeGram := by
  ext k l
  rw [transpose_mul_wedgeGram_mul_apply, det_expand]
  fin_cases k <;> fin_cases l <;>
    simp [wedge2, wedgeGram, wedgeFst, wedgeSnd] <;> ring

@[expose] def pf4 (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) : R :=
  M (.inl 0) (.inl 1) * M (.inr 0) (.inr 1) - M (.inl 0) (.inr 0) * M (.inl 1) (.inr 1) +
    M (.inl 0) (.inr 1) * M (.inl 1) (.inr 0)

theorem pf4_transpose_mul_wedgeJ_mul (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) :
    pf4 (Aᵀ * wedgeJ R * A) = - A.det := by
  rw [det_expand]
  simp [pf4, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply]
  ring

theorem pf4_smul_wedgeJ (μ : R) : pf4 (μ • wedgeJ R) = - μ ^ 2 := by
  simp [pf4, Matrix.fromBlocks]
  ring

theorem det_eq_sq_of_similitude {A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R} {μ : R}
    (h : Aᵀ * wedgeJ R * A = μ • wedgeJ R) : A.det = μ ^ 2 := by
  have := pf4_transpose_mul_wedgeJ_mul A
  rw [h, pf4_smul_wedgeJ] at this
  linear_combination this

@[expose] def wedgeBasis : Matrix (Fin 6) (Fin 5) R :=
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1; 0, 0, 0, 0, -1]

@[expose] def wedgeCoord : Matrix (Fin 5) (Fin 6) R :=
  !![1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0]

@[expose] def wedgeEps : Matrix (Fin 1) (Fin 6) R := !![0, 0, 0, 0, 1, 1]

@[expose] def wedgeLast : Matrix (Fin 6) (Fin 1) R := !![0; 0; 0; 0; 0; 1]

@[expose] def quadGram5 (R : Type*) [CommRing R] : Matrix (Fin 5) (Fin 5) R :=
  !![0, 1, 0, 0, 0; 1, 0, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 2]

@[expose] def wedgeRestrict (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) :
    Matrix (Fin 5) (Fin 5) R :=
  wedgeCoord * wedge2 A * wedgeBasis

theorem wedgeCoord_mul_wedgeBasis :
    (wedgeCoord * wedgeBasis : Matrix (Fin 5) (Fin 5) R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wedgeCoord, wedgeBasis, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

theorem wedgeBasis_mul_wedgeCoord :
    (wedgeBasis * wedgeCoord : Matrix (Fin 6) (Fin 6) R) = 1 - wedgeLast * wedgeEps := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wedgeCoord, wedgeBasis, wedgeLast, wedgeEps, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.one_apply]

theorem wedgeEps_mul_wedgeBasis : (wedgeEps * wedgeBasis : Matrix (Fin 1) (Fin 5) R) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wedgeEps, wedgeBasis, Matrix.mul_apply, Fin.sum_univ_succ]

theorem wedgeBasis_gram :
    (wedgeBasisᵀ * wedgeGram * wedgeBasis : Matrix (Fin 5) (Fin 5) R) = quadGram5 R := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wedgeBasis, wedgeGram, quadGram5, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem wedgeEps_mul_wedge2 {A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R} {μ : R}
    (h : Aᵀ * wedgeJ R * A = μ • wedgeJ R) :
    (wedgeEps * wedge2 A : Matrix (Fin 1) (Fin 6) R) = μ • wedgeEps := by
  have e01 := congrFun (congrFun h (.inl 0)) (.inl 1)
  have e23 := congrFun (congrFun h (.inr 0)) (.inr 1)
  have e02 := congrFun (congrFun h (.inl 0)) (.inr 0)
  have e13 := congrFun (congrFun h (.inl 1)) (.inr 1)
  have e03 := congrFun (congrFun h (.inl 0)) (.inr 1)
  have e12 := congrFun (congrFun h (.inl 1)) (.inr 0)
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply] at e01 e23 e02
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply] at e13 e03 e12
  ext i q
  fin_cases i <;> fin_cases q <;>
    simp [wedgeEps, wedge2, wedgeFst, wedgeSnd, Matrix.mul_apply, Fin.sum_univ_succ]
  · linear_combination e01
  · linear_combination e23
  · linear_combination e03
  · linear_combination e12
  · linear_combination e02
  · linear_combination e13

theorem wedge2_mul_wedgeBasis {A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R} {μ : R}
    (h : Aᵀ * wedgeJ R * A = μ • wedgeJ R) :
    wedge2 A * wedgeBasis = wedgeBasis * wedgeRestrict A := by
  have h1 : wedgeEps * (wedge2 A * wedgeBasis) = (0 : Matrix (Fin 1) (Fin 5) R) := by
    rw [← Matrix.mul_assoc, wedgeEps_mul_wedge2 h, Matrix.smul_mul, wedgeEps_mul_wedgeBasis,
      smul_zero]
  have h2 : (wedgeBasis * wedgeCoord) * (wedge2 A * wedgeBasis) = wedge2 A * wedgeBasis := by
    rw [wedgeBasis_mul_wedgeCoord, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, h1,
      Matrix.mul_zero, sub_zero]
  rw [← h2, wedgeRestrict]
  simp only [Matrix.mul_assoc]

theorem wedge2_apply_zero_zero (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) :
    wedge2 A 0 0 =
      A (.inl 0) (.inl 0) * A (.inl 1) (.inl 1) - A (.inl 0) (.inl 1) * A (.inl 1) (.inl 0) := by
  simp [wedge2, wedgeFst, wedgeSnd]

theorem wedgeRestrict_apply_zero_zero (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) :
    wedgeRestrict A 0 0 = wedge2 A 0 0 := by
  rw [wedgeRestrict, Matrix.mul_apply]
  simp only [Fin.sum_univ_six, Matrix.mul_apply, Fin.sum_univ_five]
  simp [wedgeCoord, wedgeBasis]

theorem wedgeRestrict_mul (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
    {B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R} {ν : R}
    (hB : Bᵀ * wedgeJ R * B = ν • wedgeJ R) :
    wedgeRestrict (A * B) = wedgeRestrict A * wedgeRestrict B := by
  have h1 : wedgeRestrict (A * B) =
      (wedgeCoord : Matrix (Fin 5) (Fin 6) R) * wedge2 A * (wedge2 B * wedgeBasis) := by
    rw [wedgeRestrict, wedge2_mul]
    simp only [Matrix.mul_assoc]
  rw [h1, wedge2_mul_wedgeBasis hB, wedgeRestrict, wedgeRestrict]
  simp only [Matrix.mul_assoc]

theorem wedgeRestrict_one :
    wedgeRestrict (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) = 1 := by
  rw [wedgeRestrict, wedge2_one, Matrix.mul_one, wedgeCoord_mul_wedgeBasis]

theorem wedgeRestrict_smul (c : R) (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) :
    wedgeRestrict (c • A) = (c ^ 2) • wedgeRestrict A := by
  rw [wedgeRestrict, wedgeRestrict, wedge2_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem wedgeRestrict_gram {A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R} {μ : R}
    (h : Aᵀ * wedgeJ R * A = μ • wedgeJ R) :
    (wedgeRestrict A)ᵀ * quadGram5 R * wedgeRestrict A = (μ ^ 2) • quadGram5 R := by
  have hP := wedge2_mul_wedgeBasis h
  have h3 : ((wedgeBasis : Matrix (Fin 6) (Fin 5) R) * wedgeRestrict A)ᵀ *
      (wedgeGram : Matrix (Fin 6) (Fin 6) R) * (wedgeBasis * wedgeRestrict A) =
      (wedgeRestrict A)ᵀ * (wedgeBasisᵀ * (wedgeGram : Matrix (Fin 6) (Fin 6) R) * wedgeBasis) *
        wedgeRestrict A := by
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  have h4 : (wedge2 A * (wedgeBasis : Matrix (Fin 6) (Fin 5) R))ᵀ *
      (wedgeGram : Matrix (Fin 6) (Fin 6) R) * (wedge2 A * wedgeBasis) =
      wedgeBasisᵀ * ((wedge2 A)ᵀ * (wedgeGram : Matrix (Fin 6) (Fin 6) R) * wedge2 A) *
        wedgeBasis := by
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [← wedgeBasis_gram, ← h3, ← hP, h4, wedge2_gram, det_eq_sq_of_similitude h,
    Matrix.mul_smul, Matrix.smul_mul]

end CFSG.ClassicalGroups.Symplectic.WedgeTwo
