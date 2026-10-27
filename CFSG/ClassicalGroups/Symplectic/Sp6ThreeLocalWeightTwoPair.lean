module

public import CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocalOrthLevi

public section

namespace CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal

open Matrix CFSG.Open CFSG.LinearAlgebra
open scoped MatrixGroups

variable {K : Type} [Field K]

@[expose] def weightTwoConj (s : SL(2, K)) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K :=
  tensorMatrix 1 !![1, 0, 0; 1, 1, 0; 0, 0, 1] +
    tensorMatrix (s : Matrix (Fin 2) (Fin 2) K) !![0, 1, 0; 0, 1, 0; 0, 0, 0]

@[expose] def weightTwoConjInv (s : SL(2, K)) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K :=
  tensorMatrix 1 !![1, 0, 0; 1, 1, 0; 0, 0, 1] +
    tensorMatrix (s : Matrix (Fin 2) (Fin 2) K) !![1, 1, 0; 0, 0, 0; 0, 0, 0]

private theorem wt2_X_mul_X [CharP K 2] :
    (!![1, 0, 0; 1, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) *
      !![1, 0, 0; 1, 1, 0; 0, 0, 1] = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  linear_combination h2

private theorem wt2_Y_mul_X_add [CharP K 2] :
    (!![0, 1, 0; 0, 1, 0; 0, 0, 0] : Matrix (Fin 3) (Fin 3) K) * !![1, 0, 0; 1, 1, 0; 0, 0, 1] +
      !![1, 0, 0; 1, 1, 0; 0, 0, 1] * !![1, 1, 0; 0, 0, 0; 0, 0, 0] = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> linear_combination h2

private theorem wt2_Y_mul_Y' :
    (!![0, 1, 0; 0, 1, 0; 0, 0, 0] : Matrix (Fin 3) (Fin 3) K) *
      !![1, 1, 0; 0, 0, 0; 0, 0, 0] = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem wt2_transpose_X_mul_X_add [CharP K 2] :
    (!![1, 0, 0; 1, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K)ᵀ * !![1, 0, 0; 1, 1, 0; 0, 0, 1] +
      !![0, 0, 0; 0, 1, 0; 0, 0, 0] = leviForm := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [leviForm, Matrix.mul_apply, Fin.sum_univ_three] <;>
    linear_combination h2

private theorem wt2_transpose_X_mul_Y [CharP K 2] :
    (!![1, 0, 0; 1, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K)ᵀ * !![0, 1, 0; 0, 1, 0; 0, 0, 0] =
      !![0, 0, 0; 0, 1, 0; 0, 0, 0] := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  linear_combination h2

private theorem wt2_transpose_Y_mul_X [CharP K 2] :
    (!![0, 1, 0; 0, 1, 0; 0, 0, 0] : Matrix (Fin 3) (Fin 3) K)ᵀ * !![1, 0, 0; 1, 1, 0; 0, 0, 1] =
      !![0, 0, 0; 0, 1, 0; 0, 0, 0] := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  linear_combination h2

private theorem wt2_transpose_Y_mul_Y [CharP K 2] :
    (!![0, 1, 0; 0, 1, 0; 0, 0, 0] : Matrix (Fin 3) (Fin 3) K)ᵀ *
      !![0, 1, 0; 0, 1, 0; 0, 0, 0] = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  linear_combination h2

private theorem wt2_J₂_mul_add_transpose_mul (A : Matrix (Fin 2) (Fin 2) K) :
    !![0, 1; -1, 0] * A + Aᵀ * !![0, 1; -1, 0] = Matrix.trace A • !![0, 1; -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.vecMul, dotProduct] <;>
    ring

theorem weightTwoConj_mul_inv [CharP K 2] (s : SL(2, K)) :
    weightTwoConj s * weightTwoConjInv s = 1 := by
  simp only [weightTwoConj, weightTwoConjInv, Matrix.add_mul, Matrix.mul_add, tensorMatrix_mul,
    Matrix.one_mul, Matrix.mul_one, wt2_X_mul_X, wt2_Y_mul_Y', tensorMatrix_zero_right, add_zero]
  rw [add_assoc, ← tensorMatrix_add_right, wt2_Y_mul_X_add, tensorMatrix_zero_right, add_zero,
    tensorMatrix_one]

theorem weightTwoConjInv_mul [CharP K 2] (s : SL(2, K)) :
    weightTwoConjInv s * weightTwoConj s = 1 :=
  mul_eq_one_comm.mp (weightTwoConj_mul_inv s)

theorem transpose_weightTwoConj_mul [CharP K 2] {s : SL(2, K)} (hs : IsCubeRootBlock s) :
    (weightTwoConj s)ᵀ * fromBlocks 0 1 (-1) 0 * weightTwoConj s =
      tensorMatrix !![0, 1; -1, 0] leviForm := by
  have htr : !![0, 1; -1, 0] * (s : Matrix (Fin 2) (Fin 2) K) +
      (s : Matrix (Fin 2) (Fin 2) K)ᵀ * !![0, 1; -1, 0] = !![0, 1; -1, 0] := by
    rw [wt2_J₂_mul_add_transpose_mul, hs.trace_eq, CharTwo.neg_eq, one_smul]
  calc (weightTwoConj s)ᵀ * fromBlocks 0 1 (-1) 0 * weightTwoConj s
      = tensorMatrix !![0, 1; -1, 0]
            ((!![1, 0, 0; 1, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K)ᵀ *
              !![1, 0, 0; 1, 1, 0; 0, 0, 1]) +
          tensorMatrix (!![0, 1; -1, 0] * (s : Matrix (Fin 2) (Fin 2) K) +
            (s : Matrix (Fin 2) (Fin 2) K)ᵀ * !![0, 1; -1, 0]) !![0, 0, 0; 0, 1, 0; 0, 0, 0] +
          tensorMatrix ((s : Matrix (Fin 2) (Fin 2) K)ᵀ * !![0, 1; -1, 0] *
            (s : Matrix (Fin 2) (Fin 2) K))
            ((!![0, 1, 0; 0, 1, 0; 0, 0, 0] : Matrix (Fin 3) (Fin 3) K)ᵀ *
              !![0, 1, 0; 0, 1, 0; 0, 0, 0]) := by
        rw [fromBlocks_form_eq_tensorMatrix, tensorMatrix_add_left]
        simp only [weightTwoConj, Matrix.transpose_add, tensorMatrix_transpose,
          Matrix.transpose_one, Matrix.add_mul, Matrix.mul_add, tensorMatrix_mul, Matrix.one_mul,
          Matrix.mul_one, wt2_transpose_X_mul_Y, wt2_transpose_Y_mul_X]
        abel
    _ = tensorMatrix !![0, 1; -1, 0] leviForm := by
        rw [htr, wt2_transpose_Y_mul_Y, tensorMatrix_zero_right, add_zero,
          ← tensorMatrix_add_right, wt2_transpose_X_mul_X_add]

private theorem wt2_commute_tensorMatrix {A A₁ : Matrix (Fin 2) (Fin 2) K}
    {B B₁ : Matrix (Fin 3) (Fin 3) K} (hA : Commute A A₁) (hB : Commute B B₁) :
    Commute (tensorMatrix A B) (tensorMatrix A₁ B₁) := by
  unfold Commute SemiconjBy
  rw [tensorMatrix_mul, tensorMatrix_mul, hA.eq, hB.eq]

private theorem wt2_commute_tensorMatrix_of_mul_eq_zero (A A₁ : Matrix (Fin 2) (Fin 2) K)
    {B B₁ : Matrix (Fin 3) (Fin 3) K} (h₁ : B * B₁ = 0) (h₂ : B₁ * B = 0) :
    Commute (tensorMatrix A B) (tensorMatrix A₁ B₁) := by
  unfold Commute SemiconjBy
  rw [tensorMatrix_mul, tensorMatrix_mul, h₁, h₂, tensorMatrix_zero_right, tensorMatrix_zero_right]

private theorem wt2_commute_D12 {B : Matrix (Fin 3) (Fin 3) K} (h02 : B 0 2 = 0) (h12 : B 1 2 = 0)
    (h20 : B 2 0 = 0) (h21 : B 2 1 = 0) : Commute (diagonal ![1, 1, 0]) B := by
  unfold Commute SemiconjBy
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h02, h12, h20, h21]

private theorem wt2_commute_D3 {B : Matrix (Fin 3) (Fin 3) K} (h02 : B 0 2 = 0) (h12 : B 1 2 = 0)
    (h20 : B 2 0 = 0) (h21 : B 2 1 = 0) : Commute (diagonal ![0, 0, 1]) B := by
  unfold Commute SemiconjBy
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h02, h12, h20, h21]

private theorem wt2_D3_mul_eq_zero {B : Matrix (Fin 3) (Fin 3) K} (h20 : B 2 0 = 0)
    (h21 : B 2 1 = 0) (h22 : B 2 2 = 0) : diagonal ![0, 0, 1] * B = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h20, h21, h22]

private theorem wt2_mul_D3_eq_zero {B : Matrix (Fin 3) (Fin 3) K} (h02 : B 0 2 = 0)
    (h12 : B 1 2 = 0) (h22 : B 2 2 = 0) : B * diagonal ![0, 0, 1] = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h02, h12, h22]

theorem commute_blockMatrix_weightTwoConj (s : SL(2, K)) {A : Matrix (Fin 2) (Fin 2) K}
    (hA : Commute A (s : Matrix (Fin 2) (Fin 2) K)) (A' : Matrix (Fin 2) (Fin 2) K) :
    Commute (blockMatrix ![A, A, A']) (weightTwoConj s) := by
  rw [blockMatrix_pair, weightTwoConj]
  refine ((wt2_commute_tensorMatrix (Commute.one_right A) ?_).add_right
    (wt2_commute_tensorMatrix hA ?_)).add_left
    ((wt2_commute_tensorMatrix (Commute.one_right A') ?_).add_right
      (wt2_commute_tensorMatrix_of_mul_eq_zero _ _ ?_ ?_))
  · exact wt2_commute_D12 (by simp) (by simp) (by simp) (by simp)
  · exact wt2_commute_D12 (by simp) (by simp) (by simp) (by simp)
  · exact wt2_commute_D3 (by simp) (by simp) (by simp) (by simp)
  · exact wt2_D3_mul_eq_zero (by simp) (by simp) (by simp)
  · exact wt2_mul_D3_eq_zero (by simp) (by simp) (by simp)

theorem commute_blockMatrix_weightTwoConjInv (s : SL(2, K)) {A : Matrix (Fin 2) (Fin 2) K}
    (hA : Commute A (s : Matrix (Fin 2) (Fin 2) K)) (A' : Matrix (Fin 2) (Fin 2) K) :
    Commute (blockMatrix ![A, A, A']) (weightTwoConjInv s) := by
  rw [blockMatrix_pair, weightTwoConjInv]
  refine ((wt2_commute_tensorMatrix (Commute.one_right A) ?_).add_right
    (wt2_commute_tensorMatrix hA ?_)).add_left
    ((wt2_commute_tensorMatrix (Commute.one_right A') ?_).add_right
      (wt2_commute_tensorMatrix_of_mul_eq_zero _ _ ?_ ?_))
  · exact wt2_commute_D12 (by simp) (by simp) (by simp) (by simp)
  · exact wt2_commute_D12 (by simp) (by simp) (by simp) (by simp)
  · exact wt2_commute_D3 (by simp) (by simp) (by simp) (by simp)
  · exact wt2_D3_mul_eq_zero (by simp) (by simp) (by simp)
  · exact wt2_mul_D3_eq_zero (by simp) (by simp) (by simp)

theorem commute_blockMatrix_tensorMatrix_leviMat (A A' : Matrix (Fin 2) (Fin 2) K)
    (z : SL(2, K)) : Commute (blockMatrix ![A, A, A']) (tensorMatrix 1 (leviMat z)) := by
  rw [blockMatrix_pair]
  exact (wt2_commute_tensorMatrix (Commute.one_right A)
    (wt2_commute_D12 (by simp [leviMat]) (by simp [leviMat]) (by simp [leviMat])
      (by simp [leviMat]))).add_left
    (wt2_commute_tensorMatrix (Commute.one_right A')
      (wt2_commute_D3 (by simp [leviMat]) (by simp [leviMat]) (by simp [leviMat])
        (by simp [leviMat])))

end CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal
