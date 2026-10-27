module

public import CFSG.GH74.Generic.S1.FrameDefs

public section

namespace CFSG.GH74.Generic.S1

open Matrix CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank

variable (F : Type) [Field F]

theorem reflDiagMat_apply (i a b : Fin 4) :
    reflDiagMat F i a b = if a = b then (if a = i then (-1 : F) else 1) else 0 := by
  simp [reflDiagMat, Matrix.diagonal_apply]

@[expose] def monoMat : Fin 4 → Matrix (Fin 4) (Fin 4) F
  | 0 => !![0, 0, 0, -1; 0, 1, 0, 0; 0, 0, 1, 0; 1, 0, 0, 0]
  | 1 => !![1, 0, 0, 0; 0, 0, 0, -1; 0, 0, 1, 0; 0, 1, 0, 0]
  | 2 => !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, -1; 0, 0, 1, 0]
  | 3 => 1

theorem monoMat_transpose_mul (i : Fin 4) : (monoMat F i)ᵀ * monoMat F i = 1 := by
  fin_cases i <;> (ext a b; fin_cases a <;> fin_cases b <;>
    simp [monoMat, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply])

theorem monoMat_mul_transpose (i : Fin 4) : monoMat F i * (monoMat F i)ᵀ = 1 := by
  fin_cases i <;> (ext a b; fin_cases a <;> fin_cases b <;>
    simp [monoMat, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply])

theorem det_monoMat (i : Fin 4) : (monoMat F i).det = 1 := by
  have h32 : Fin.succAbove (3 : Fin 4) (2 : Fin 3) = 2 := by decide
  fin_cases i
  · simp [monoMat, Matrix.det_succ_row_zero, Fin.sum_univ_succ, h32]
    norm_num
  · simp [monoMat, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  · simp [monoMat, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  · simp [monoMat]

theorem monoMat_conj (i : Fin 4) :
    monoMat F i * reflDiagMat F 3 * (monoMat F i)ᵀ = reflDiagMat F i := by
  fin_cases i <;> (
    ext a b
    simp only [Matrix.mul_apply, Fin.sum_univ_four]
    fin_cases a <;> fin_cases b <;> simp [monoMat, reflDiagMat_apply, Matrix.one_apply])

theorem monoMat_entry (i a b : Fin 4) : monoMat F i a b = 0 ∨ monoMat F i a b = 1 ∨
    monoMat F i a b = -1 := by
  fin_cases i <;> fin_cases a <;> fin_cases b <;> simp [monoMat]

@[expose] def monoGL (i : Fin 4) : GL (Fin 4) F :=
  ⟨monoMat F i, (monoMat F i)ᵀ, monoMat_mul_transpose F i, monoMat_transpose_mul F i⟩

theorem monoGL_inv_val (i : Fin 4) :
    (((monoGL F i)⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = (monoMat F i)ᵀ := rfl

theorem monoGL_conj (i : Fin 4) :
    monoGL F i * reflDiag F 3 * (monoGL F i)⁻¹ = reflDiag F i := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, monoGL_inv_val]
  exact monoMat_conj F i

theorem monoGL_mem_statedSL (i : Fin 4) : monoGL F i ∈ StatedSL 4 F := by
  rw [statedSL_eq_detOne, mem_detOne]
  exact det_monoMat F i

theorem monoMat_map_pow {q : ℕ} (hq : Odd q) (i : Fin 4) :
    (monoMat F i).map (fun x : F => x ^ q) = monoMat F i := by
  ext a b
  rw [Matrix.map_apply]
  rcases monoMat_entry F i a b with h | h | h
  · rw [h, zero_pow (by rintro rfl; exact absurd hq (by decide))]
  · rw [h, one_pow]
  · rw [h, hq.neg_one_pow]

theorem monoGL_mem_statedSU {q : ℕ} (hq : Odd q) (i : Fin 4) : monoGL F i ∈ StatedSU 4 q F := by
  apply Subgroup.subset_closure
  refine ⟨det_monoMat F i, ?_⟩
  change ((monoMat F i).map (fun x : F => x ^ q))ᵀ * monoMat F i = 1
  rw [monoMat_map_pow F hq]
  exact monoMat_transpose_mul F i

end CFSG.GH74.Generic.S1
