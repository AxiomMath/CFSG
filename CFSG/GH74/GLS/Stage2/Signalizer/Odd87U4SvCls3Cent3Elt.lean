module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvCls3Hom

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix Module CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow
open scoped MatrixGroups commutatorElement

section Elt

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K} {A : GL (HypIndex 2 0) K}
  {E : Matrix (HypIndex 2 0) (Fin 4) K} {d : Fin 4 → h.fixedField}

@[expose] def u4Ma : Matrix (Fin 4) (Fin 4) K := Matrix.diagonal ![-1, 1, -1, 1]

@[expose] def u4Mb : Matrix (Fin 4) (Fin 4) K := !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1]

@[expose] def u4My : Matrix (Fin 4) (Fin 4) K := Matrix.diagonal ![-1, -1, 1, 1]

theorem u4Ma_mul_Mb : (u4Ma : Matrix (Fin 4) (Fin 4) K) * u4Mb = u4My * u4Mb * u4Ma := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u4Ma, u4Mb, u4My, Matrix.mul_apply, Matrix.diagonal_apply]

theorem det_u4Ma : (u4Ma : Matrix (Fin 4) (Fin 4) K).det = 1 := by
  simp [u4Ma, Matrix.det_diagonal, Fin.prod_univ_four]

theorem det_u4My : (u4My : Matrix (Fin 4) (Fin 4) K).det = 1 := by
  simp [u4My, Matrix.det_diagonal, Fin.prod_univ_four]

theorem det_u4Mb : (u4Mb : Matrix (Fin 4) (Fin 4) K).det = 1 := by
  rw [u4Mb, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero]
  have h : Fin.succAbove (1 : Fin 4) (2 : Fin 3) = 3 := by decide
  simp [h]

theorem u4Ma_bar (φ : K →+* K) : (u4Ma : Matrix (Fin 4) (Fin 4) K).map φ = u4Ma := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u4Ma]

theorem u4Mb_bar (φ : K →+* K) : (u4Mb : Matrix (Fin 4) (Fin 4) K).map φ = u4Mb := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u4Mb]

theorem u4My_bar (φ : K →+* K) : (u4My : Matrix (Fin 4) (Fin 4) K).map φ = u4My := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u4My]

theorem u4Ma_cong (e : Fin 4 → K) :
    (u4Ma : Matrix (Fin 4) (Fin 4) K)ᵀ * Matrix.diagonal e * u4Ma = Matrix.diagonal e := by
  rw [u4Ma, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  fin_cases i <;> simp

theorem u4My_cong (e : Fin 4 → K) :
    (u4My : Matrix (Fin 4) (Fin 4) K)ᵀ * Matrix.diagonal e * u4My = Matrix.diagonal e := by
  rw [u4My, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  fin_cases i <;> simp

theorem u4Mb_cong (e : Fin 4 → K) (he01 : e 0 = e 1) :
    (u4Mb : Matrix (Fin 4) (Fin 4) K)ᵀ * Matrix.diagonal e * u4Mb = Matrix.diagonal e := by
  rw [u4Mb]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply, he01]

theorem U4Frame.exists_suppMat_elt (fr : U4Frame h A E d) (hA : A ∈ hypUnitary h 2 0)
    (hAA : (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar = 1)
    {M : Matrix (Fin 4) (Fin 4) K} (hMbar : M.map h.bar = M)
    (hM : Mᵀ * Matrix.diagonal (fun i => ((d i : h.fixedField) : K)) * M =
      Matrix.diagonal (fun i => ((d i : h.fixedField) : K))) (hdet : M.det = 1) :
    ∃ g : ↥(hypSU h 2 0),
      ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
        E * M * U4Frame.fm h E d ∧
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
        ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar =
          ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
            (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) := by
  have hdetg : (suppMat E (U4Frame.fm h E d) M).det = 1 := by
    rw [det_suppMat fr.fm_mul_E, hdet]
  have hiso : ((suppMat E (U4Frame.fm h E d) M).map h.bar)ᵀ * hypGram 2 0 K *
      suppMat E (U4Frame.fm h E d) M = hypGram 2 0 K := by
    refine suppMat_isometry h.bar_bar (hypGram_conjTranspose h) fr.gi_mul_gram fr.gram_mul_gi ?_
    rw [hMbar, fr.gram]
    exact hM
  let g : ↥(hypSU h 2 0) := ⟨GeneralLinearGroup.mkOfDetNeZero (suppMat E (U4Frame.fm h E d) M)
    (by rw [hdetg]; exact one_ne_zero), mem_hypSU.2 ⟨hiso, hdetg⟩⟩
  have hg : ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
      suppMat E (U4Frame.fm h E d) M := rfl
  refine ⟨g, by rw [hg]; exact fr.suppMat_eq M, ?_⟩
  have hbar : ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar =
      suppMat (E.map h.bar) (U4Frame.gi h d * Eᵀ * hypGram 2 0 K) M := by
    rw [hg, suppMat_map, ← fr.map_fm, hMbar]
  rw [hbar, hg]
  exact mul_suppMat (E := E) (F := U4Frame.fm h E d) (D := 1) (M := M) (M' := M)
    (by rw [Matrix.mul_one]; exact fr.A_mul_conj_E)
    (by rw [Matrix.one_mul]; exact fr.fm_mul_A hA hAA) (by rw [Matrix.one_mul, Matrix.mul_one])

theorem U4Frame.frame_mul (fr : U4Frame h A E d) (M N : Matrix (Fin 4) (Fin 4) K) :
    E * M * U4Frame.fm h E d * (E * N * U4Frame.fm h E d) = E * (M * N) * U4Frame.fm h E d := by
  rw [← fr.suppMat_eq, ← fr.suppMat_eq, ← fr.suppMat_eq, ← suppMat_mul fr.fm_mul_E]

theorem U4Frame.exists_comm_elts (fr : U4Frame h A E d) (hA : A ∈ hypUnitary h 2 0)
    (hAA : (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar = 1)
    (hd01 : d 0 = d 1) :
    ∃ a b : ↥(hypSU h 2 0),
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
          ((a : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar =
        ((a : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
          (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) ∧
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
          ((b : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar =
        ((b : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
          (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) ∧
      (((⁅a, b⁆ : ↥(hypSU h 2 0)) : GL (HypIndex 2 0) K) :
          Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
        E * (u4My : Matrix (Fin 4) (Fin 4) K) * U4Frame.fm h E d := by
  have hd01' : ((d 0 : h.fixedField) : K) = ((d 1 : h.fixedField) : K) := by rw [hd01]
  obtain ⟨a, ha, haA⟩ := fr.exists_suppMat_elt hA hAA (u4Ma_bar h.bar)
    (by rw [u4Ma_cong]) det_u4Ma
  obtain ⟨b, hb, hbA⟩ := fr.exists_suppMat_elt hA hAA (u4Mb_bar h.bar)
    (u4Mb_cong _ hd01') det_u4Mb
  obtain ⟨y, hy, -⟩ := fr.exists_suppMat_elt hA hAA (u4My_bar h.bar) (by rw [u4My_cong])
    det_u4My
  refine ⟨a, b, haA, hbA, ?_⟩
  have hab : a * b = y * b * a := by
    refine Subtype.ext (Units.ext ?_)
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [ha, hb, hy, fr.frame_mul, fr.frame_mul, fr.frame_mul, u4Ma_mul_Mb]
  have hcomm : ⁅a, b⁆ = y := by
    rw [commutatorElement_def, hab]
    group
  rw [hcomm, hy]

end Elt

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
