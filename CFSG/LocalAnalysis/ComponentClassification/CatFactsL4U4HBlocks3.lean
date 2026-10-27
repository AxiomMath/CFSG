module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4HBlocks2

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace HBlocks

open Matrix CFSG.LocalAnalysis.ComponentInitial UnitaryOut UnitaryConj

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

@[expose] def lr (M : Matrix (Fin 4) (Fin 4) K) : Matrix (Fin 2) (Fin 2) K :=
  !![M 2 2, M 2 3; M 3 2, M 3 3]

theorem det_of_isBD {M : Matrix (Fin 4) (Fin 4) K} (hM : IsBD M) :
    M.det = (ul M).det * (lr M).det := by
  obtain ⟨m02, m03, m12, m13, m20, m21, m30, m31⟩ := hM
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove, ul, lr,
    m02, m03, m12, m13, m20, m21, m30, m31]
  ring

theorem ulStar_mul_lr {M : Matrix (Fin 4) (Fin 4) K} (hM : IsBD M)
    (hU : uStar h M * stdG * M = stdG) : ((ul M).map h.bar)ᵀ * lr M = 1 := by
  obtain ⟨m02, m03, m12, m13, m20, m21, m30, m31⟩ := hM
  have e02 := congrFun (congrFun hU 0) 2
  have e03 := congrFun (congrFun hU 0) 3
  have e12 := congrFun (congrFun hU 1) 2
  have e13 := congrFun (congrFun hU 1) 3
  simp [uStar, stdG, Matrix.mul_apply, Fin.sum_univ_four, m02, m03, m12, m13, m20, m21, m30,
    m31] at e02 e03 e12 e13
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ul, lr, Matrix.mul_apply, Fin.sum_univ_two, e02, e03, e12, e13]

theorem det_ul_fixed {M : Matrix (Fin 4) (Fin 4) K} (hM : IsBD M)
    (hU : uStar h M * stdG * M = stdG) (hd : M.det = 1) : h.bar (ul M).det = (ul M).det := by
  have h1 := congrArg Matrix.det (ulStar_mul_lr h hM hU)
  rw [det_mul, det_transpose, det_one] at h1
  have h2 : ((ul M).map h.bar).det = h.bar (ul M).det := by
    rw [RingHom.map_det]
    rfl
  rw [h2] at h1
  rw [det_of_isBD hM] at hd
  have h3 : (lr M).det ≠ 0 := right_ne_zero_of_mul_eq_one hd
  exact mul_right_cancel₀ h3 (h1.trans hd.symm)

theorem eq_of_blk_comm_gfix {x y β : K} (hβ : β ≠ 0)
    (hE : blk x 0 0 y * gfix β 0 = gfix β 0 * blk x 0 0 y) : x = y := by
  have e := congrFun (congrFun hE 0) 2
  simp [blk, gfix, Matrix.mul_apply, Fin.sum_univ_four] at e
  have : (x - y) * β = 0 := by linear_combination e
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hβ)

end HBlocks

end CFSG.ComponentClassification.CatFactsL4U4
