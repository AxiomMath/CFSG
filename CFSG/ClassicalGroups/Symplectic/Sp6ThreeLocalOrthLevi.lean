module

public import CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocalLevi

public section

namespace CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal

open Matrix CFSG.Open CFSG.LinearAlgebra
open scoped MatrixGroups

variable {K : Type} [Field K]

@[expose] def orthLeviConj : Matrix (Fin 3) (Fin 3) K :=
  !![1, 0, 1; 1, 1, 1; 0, 1, 1]

@[expose] def orthLeviConjInv : Matrix (Fin 3) (Fin 3) K :=
  !![0, 1, -1; -1, 1, 0; 1, -1, 1]

theorem orthLeviConj_mul_inv :
    (orthLeviConj : Matrix (Fin 3) (Fin 3) K) * orthLeviConjInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [orthLeviConj, orthLeviConjInv, Matrix.mul_apply, Fin.sum_univ_three]

theorem orthLeviConjInv_mul :
    (orthLeviConjInv : Matrix (Fin 3) (Fin 3) K) * orthLeviConj = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [orthLeviConj, orthLeviConjInv, Matrix.mul_apply, Fin.sum_univ_three]

@[expose] def leviForm : Matrix (Fin 3) (Fin 3) K :=
  !![0, 1, 0; -1, 0, 0; 0, 0, 1]

theorem transpose_leviMat_mul_leviForm_mul (z : SL(2, K)) :
    (leviMat z)ᵀ * leviForm * leviMat z = leviForm := by
  have hdet : (z : Matrix (Fin 2) (Fin 2) K) 0 0 * (z : Matrix (Fin 2) (Fin 2) K) 1 1 -
      (z : Matrix (Fin 2) (Fin 2) K) 0 1 * (z : Matrix (Fin 2) (Fin 2) K) 1 0 = 1 := by
    rw [← Matrix.det_fin_two]
    exact z.2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leviMat, leviForm, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first | ring1 | linear_combination hdet | linear_combination -hdet

theorem transpose_orthLeviConj_mul [CharP K 2] :
    (orthLeviConj : Matrix (Fin 3) (Fin 3) K)ᵀ * orthLeviConj = leviForm := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [orthLeviConj, leviForm, Matrix.mul_apply, Fin.sum_univ_three] <;>
    linear_combination h2

@[expose] def orthLeviMat (z : SL(2, K)) : Matrix (Fin 3) (Fin 3) K :=
  orthLeviConj * leviMat z * orthLeviConjInv

theorem orthLeviMat_one : orthLeviMat (1 : SL(2, K)) = 1 := by
  rw [orthLeviMat, leviMat_one, Matrix.mul_one, orthLeviConj_mul_inv]

theorem orthLeviMat_mul (z w : SL(2, K)) :
    orthLeviMat (z * w) = orthLeviMat z * orthLeviMat w := by
  simp only [orthLeviMat, leviMat_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc orthLeviConjInv orthLeviConj, orthLeviConjInv_mul, Matrix.one_mul]

theorem transpose_orthLeviMat_mul [CharP K 2] (z : SL(2, K)) :
    (orthLeviMat z)ᵀ * orthLeviMat z = 1 := by
  have hP : (orthLeviConj : Matrix (Fin 3) (Fin 3) K)ᵀ * orthLeviConj = leviForm :=
    transpose_orthLeviConj_mul
  calc (orthLeviMat z)ᵀ * orthLeviMat z
      = (orthLeviConjInv : Matrix (Fin 3) (Fin 3) K)ᵀ *
          ((leviMat z)ᵀ * ((orthLeviConj : Matrix (Fin 3) (Fin 3) K)ᵀ * orthLeviConj) *
            leviMat z) * orthLeviConjInv := by
        simp only [orthLeviMat, Matrix.transpose_mul, Matrix.mul_assoc]
    _ = ((orthLeviConj : Matrix (Fin 3) (Fin 3) K) * orthLeviConjInv)ᵀ *
          (orthLeviConj * orthLeviConjInv) := by
        rw [hP, transpose_leviMat_mul_leviForm_mul, ← hP]
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [orthLeviConj_mul_inv, Matrix.transpose_one, Matrix.one_mul]

@[expose] noncomputable def weightThreeSL [CharP K 2] : SL(2, K) →* StatedSp 3 K where
  toFun z := orthBlock (orthLeviMat z) (transpose_orthLeviMat_mul z)
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    change tensorMatrix 1 (orthLeviMat (1 : SL(2, K))) = 1
    rw [orthLeviMat_one, tensorMatrix_one]
  map_mul' z w := by
    apply Subtype.ext
    apply Units.ext
    change tensorMatrix 1 (orthLeviMat (z * w)) =
      tensorMatrix 1 (orthLeviMat z) * tensorMatrix 1 (orthLeviMat w)
    rw [orthLeviMat_mul, tensorMatrix_mul, Matrix.one_mul]

theorem coe_weightThreeSL [CharP K 2] (z : SL(2, K)) :
    (((weightThreeSL z : StatedSp 3 K) : GL (Fin 3 ⊕ Fin 3) K) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) = tensorMatrix 1 (orthLeviMat z) :=
  rfl

theorem weightThreeSL_injective [CharP K 2] :
    Function.Injective (weightThreeSL : SL(2, K) →* StatedSp 3 K) := by
  rw [injective_iff_map_eq_one]
  intro z hz
  have h := congrArg (fun g : StatedSp 3 K => (((g : GL (Fin 3 ⊕ Fin 3) K) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K))) hz
  simp only [coe_weightThreeSL] at h
  have hM : orthLeviMat z = 1 := by
    ext i j
    have := congrFun (congrFun h (Sum.inl i)) (Sum.inl j)
    simpa [tensorMatrix, Matrix.one_apply] using this
  have hL : leviMat z = 1 := by
    have h' : orthLeviConjInv * orthLeviMat z * orthLeviConj = leviMat z := by
      simp only [orthLeviMat, ← Matrix.mul_assoc, orthLeviConjInv_mul, Matrix.one_mul]
      rw [Matrix.mul_assoc, orthLeviConjInv_mul, Matrix.mul_one]
    rw [← h', hM, Matrix.mul_one, orthLeviConjInv_mul]
  have h00 := congrFun (congrFun hL 0) 0
  have h01 := congrFun (congrFun hL 0) 1
  have h10 := congrFun (congrFun hL 1) 0
  have h11 := congrFun (congrFun hL 1) 1
  simp [leviMat] at h00 h01 h10 h11
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]

theorem commute_c₀_point_111_weightThreeSL [CharP K 2] {s : SL(2, K)} (hs : IsCubeRootBlock s)
    (z : SL(2, K)) : Commute (c₀ hs (Multiplicative.ofAdd ![1, 1, 1])) (weightThreeSL z) :=
  commute_c₀_point_111_orthBlock hs (orthLeviMat z) (transpose_orthLeviMat_mul z)

end CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal
