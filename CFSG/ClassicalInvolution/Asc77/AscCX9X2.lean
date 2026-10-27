module

public import CFSG.ClassicalInvolution.Asc77.AscCX9X1
public import CFSG.ClassicalGroups.Symplectic.Model
public import CFSG.LieType.Universal.SymplecticExtras.Matrices

public noncomputable section

namespace CFSG.ClassicalInvolution.Asc77.CX.MF2L

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def spIdx : Fin 4 → Fin 2 ⊕ Fin 2 :=
  ![Sum.inl 0, Sum.inr 0, Sum.inl 1, Sum.inr 1]

theorem spIdx_bijective : Function.Bijective spIdx := by
  decide

@[expose] def spIdxEquiv : Fin 4 ≃ Fin 2 ⊕ Fin 2 :=
  Equiv.ofBijective spIdx spIdx_bijective

theorem coe_spIdxEquiv : (spIdxEquiv : Fin 4 → Fin 2 ⊕ Fin 2) = spIdx := rfl

@[expose] def dVec (m n : F) : Fin 4 → F :=
  ![1, -m, 1, -n]

theorem diagonal_dVec_mul_inv {m n : F} (hm : m ≠ 0) (hn : n ≠ 0) :
    diagonal (dVec m n) * diagonal (dVec m⁻¹ n⁻¹) = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext k
  fin_cases k <;> simp [dVec, hm, hn]

theorem diagonal_dVec_inv_mul {m n : F} (hm : m ≠ 0) (hn : n ≠ 0) :
    diagonal (dVec m⁻¹ n⁻¹) * diagonal (dVec m n) = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext k
  fin_cases k <;> simp [dVec, hm, hn]

@[expose] def kMat (m n : F) (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) :
    Matrix (Fin 4) (Fin 4) F :=
  diagonal (dVec m n) * X.submatrix spIdx spIdx * diagonal (dVec m⁻¹ n⁻¹)

theorem kMat_mul {m n : F} (hm : m ≠ 0) (hn : n ≠ 0)
    (X Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) :
    kMat m n (X * Y) = kMat m n X * kMat m n Y := by
  have hsub : (X * Y).submatrix spIdx spIdx =
      X.submatrix spIdx spIdx * Y.submatrix spIdx spIdx :=
    (submatrix_mul_equiv X Y spIdx spIdxEquiv spIdx).symm
  rw [kMat, kMat, kMat, hsub]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (diagonal (dVec m⁻¹ n⁻¹)) (diagonal (dVec m n)),
    diagonal_dVec_inv_mul hm hn, Matrix.one_mul]

theorem kMat_one {m n : F} (hm : m ≠ 0) (hn : n ≠ 0) :
    kMat m n (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 1 := by
  have h1 : (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).submatrix spIdx spIdx = 1 :=
    submatrix_one_equiv spIdxEquiv
  rw [kMat, h1, Matrix.mul_one, diagonal_dVec_mul_inv hm hn]

theorem det_kMat {m n : F} (hm : m ≠ 0) (hn : n ≠ 0)
    (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) : (kMat m n X).det = X.det := by
  have hD : (diagonal (dVec m⁻¹ n⁻¹)).det * (diagonal (dVec m n)).det = 1 := by
    rw [← det_mul, diagonal_dVec_inv_mul hm hn, det_one]
  have h2 : (X.submatrix spIdx spIdx).det = X.det := det_submatrix_equiv_self spIdxEquiv X
  rw [kMat, det_mul, det_mul, h2, mul_comm _ X.det, mul_assoc, mul_comm _ (det _), hD, mul_one]

theorem mat_mem_symplecticGroup (x : StatedSp 2 F) :
    mat 2 F x ∈ Matrix.symplecticGroup (Fin 2) F := by
  rw [mat_apply]
  exact TauCeti.GLSymplectic.mem_iff_mem_symplecticGroup.mp
    ((CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic (n := 2) (K := F)).le x.2)

theorem det_mat_sp (x : StatedSp 2 F) : (mat 2 F x).det = 1 :=
  SymplecticGroup.det_eq_one (mat_mem_symplecticGroup x)

@[expose] def kappa {m n : F} (hm : m ≠ 0) (hn : n ≠ 0) : StatedSp 2 F →* SL(4, F) where
  toFun x := ⟨kMat m n (mat 2 F x), by rw [det_kMat hm hn, det_mat_sp]⟩
  map_one' := Subtype.ext (by
    change kMat m n (mat 2 F 1) = 1
    rw [map_one, kMat_one hm hn])
  map_mul' x y := Subtype.ext (by
    change kMat m n (mat 2 F (x * y)) = kMat m n (mat 2 F x) * kMat m n (mat 2 F y)
    rw [map_mul, kMat_mul hm hn])

theorem coe_kappa {m n : F} (hm : m ≠ 0) (hn : n ≠ 0) (x : StatedSp 2 F) :
    ((kappa hm hn x : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = kMat m n (mat 2 F x) := rfl

theorem kMat_injective {m n : F} (hm : m ≠ 0) (hn : n ≠ 0) :
    Function.Injective (kMat (F := F) m n) := by
  intro X Y h
  have h1 : X.submatrix spIdx spIdx = Y.submatrix spIdx spIdx := by
    have e : ∀ Z : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F, Z.submatrix spIdx spIdx =
        diagonal (dVec m⁻¹ n⁻¹) * kMat m n Z * diagonal (dVec m n) := by
      intro Z
      rw [kMat]
      simp only [Matrix.mul_assoc]
      rw [diagonal_dVec_inv_mul hm hn, Matrix.mul_one, ← Matrix.mul_assoc,
        diagonal_dVec_inv_mul hm hn, Matrix.one_mul]
    rw [e, e, h]
  have h2 := congrArg (fun Z => Z.submatrix spIdxEquiv.symm spIdxEquiv.symm) h1
  simp only [Matrix.submatrix_submatrix, ← coe_spIdxEquiv, Equiv.self_comp_symm,
    Matrix.submatrix_id_id] at h2
  exact h2

theorem kappa_injective {m n : F} (hm : m ≠ 0) (hn : n ≠ 0) :
    Function.Injective (kappa (F := F) hm hn) := fun _ _ h =>
  mat_injective (kMat_injective hm hn (congrArg Subtype.val h))

theorem J_submatrix : (Matrix.J (Fin 2) F).submatrix spIdx spIdx = spForm (-1) (-1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.J, spIdx, spForm]

theorem dVec_conj (m n : F) :
    diagonal (dVec m n) * spForm (-1) (-1) * diagonal (dVec m n) = spForm m n := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dVec, spForm, Matrix.mul_apply, Fin.sum_univ_four]

theorem dVec_inv_conj {m n : F} (hm : m ≠ 0) (hn : n ≠ 0) :
    diagonal (dVec m⁻¹ n⁻¹) * spForm m n * diagonal (dVec m⁻¹ n⁻¹) = spForm (-1) (-1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dVec, spForm, Matrix.mul_apply, Fin.sum_univ_four, hm, hn]

theorem submatrix_congr_eq {ι : Type} [Fintype ι] [DecidableEq ι] (e : Fin 4 ≃ ι)
    (X J : Matrix ι ι F) :
    (X * J * Xᵀ).submatrix e e =
      X.submatrix e e * J.submatrix e e * (X.submatrix e e)ᵀ := by
  rw [Matrix.transpose_submatrix, submatrix_mul_equiv X J e e e,
    submatrix_mul_equiv (X * J) Xᵀ e e e]

theorem kappa_mem_spM {m n : F} (hm : m ≠ 0) (hn : n ≠ 0) (x : StatedSp 2 F) :
    kappa hm hn x ∈ spM (spForm m n) := by
  rw [mem_spM, coe_kappa, kMat]
  have hX := SymplecticGroup.mem_iff.mp (mat_mem_symplecticGroup x)
  have hsub := submatrix_congr_eq spIdxEquiv (mat 2 F x) (Matrix.J (Fin 2) F)
  rw [hX, coe_spIdxEquiv, J_submatrix] at hsub
  rw [Matrix.transpose_mul, Matrix.transpose_mul, diagonal_transpose, diagonal_transpose]
  calc diagonal (dVec m n) * (mat 2 F x).submatrix spIdx spIdx * diagonal (dVec m⁻¹ n⁻¹) *
        spForm m n * (diagonal (dVec m⁻¹ n⁻¹) *
          (((mat 2 F x).submatrix spIdx spIdx)ᵀ * diagonal (dVec m n)))
      = diagonal (dVec m n) * ((mat 2 F x).submatrix spIdx spIdx *
          (diagonal (dVec m⁻¹ n⁻¹) * spForm m n * diagonal (dVec m⁻¹ n⁻¹)) *
            ((mat 2 F x).submatrix spIdx spIdx)ᵀ) * diagonal (dVec m n) := by
        simp only [Matrix.mul_assoc]
    _ = spForm m n := by rw [dVec_inv_conj hm hn, ← hsub, dVec_conj]

theorem kappa_range {m n : F} (hm : m ≠ 0) (hn : n ≠ 0) :
    (kappa (F := F) hm hn).range = spM (spForm m n) := by
  refine le_antisymm (by rintro _ ⟨x, rfl⟩; exact kappa_mem_spM hm hn x) fun g hg => ?_
  set Y := diagonal (dVec m⁻¹ n⁻¹) * (g : Matrix (Fin 4) (Fin 4) F) * diagonal (dVec m n)
    with hY
  set X := Y.submatrix spIdxEquiv.symm spIdxEquiv.symm with hXdef
  have hXY : X.submatrix spIdx spIdx = Y := by
    rw [hXdef, Matrix.submatrix_submatrix, ← coe_spIdxEquiv, Equiv.symm_comp_self,
      Matrix.submatrix_id_id]
  have hYJ : Y * spForm (-1) (-1) * Yᵀ = spForm (-1) (-1) := by
    have hg' := mem_spM.mp hg
    rw [hY, Matrix.transpose_mul, Matrix.transpose_mul, diagonal_transpose, diagonal_transpose]
    calc diagonal (dVec m⁻¹ n⁻¹) * (g : Matrix (Fin 4) (Fin 4) F) * diagonal (dVec m n) *
          spForm (-1) (-1) * (diagonal (dVec m n) * ((g : Matrix (Fin 4) (Fin 4) F)ᵀ *
            diagonal (dVec m⁻¹ n⁻¹)))
        = diagonal (dVec m⁻¹ n⁻¹) * ((g : Matrix (Fin 4) (Fin 4) F) *
            (diagonal (dVec m n) * spForm (-1) (-1) * diagonal (dVec m n)) *
              (g : Matrix (Fin 4) (Fin 4) F)ᵀ) * diagonal (dVec m⁻¹ n⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = spForm (-1) (-1) := by rw [dVec_conj, hg', dVec_inv_conj hm hn]
  have hXJ : X * Matrix.J (Fin 2) F * Xᵀ = Matrix.J (Fin 2) F := by
    have h1 : (X * Matrix.J (Fin 2) F * Xᵀ).submatrix spIdxEquiv spIdxEquiv =
        (Matrix.J (Fin 2) F).submatrix spIdxEquiv spIdxEquiv := by
      rw [submatrix_congr_eq, coe_spIdxEquiv, hXY, J_submatrix, hYJ]
    have h2 := congrArg (fun Z => Z.submatrix spIdxEquiv.symm spIdxEquiv.symm) h1
    simpa only [Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id]
      using h2
  have hdet : X.det = 1 := by
    have h1 : X.det = Y.det := det_submatrix_equiv_self spIdxEquiv.symm Y
    have hD : (diagonal (dVec m⁻¹ n⁻¹)).det * (diagonal (dVec m n)).det = 1 := by
      rw [← det_mul, diagonal_dVec_inv_mul hm hn, det_one]
    rw [h1, hY, det_mul, det_mul, g.2, mul_one, hD]
  have hsymp : X ∈ Matrix.symplecticGroup (Fin 2) F := SymplecticGroup.mem_iff.mpr hXJ
  set A : GL (Fin 2 ⊕ Fin 2) F :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero X (by rw [hdet]; exact one_ne_zero) with hA
  have hAsp : A ∈ StatedSp 2 F :=
    Subgroup.subset_closure
      ((CFSG.ClassicalGroups.Symplectic.blueprintGram_iff_mem_symplecticGroup X).mpr hsymp)
  refine ⟨⟨A, hAsp⟩, Subtype.ext ?_⟩
  rw [coe_kappa, mat_apply]
  show kMat m n X = _
  rw [kMat, hXY, hY]
  calc diagonal (dVec m n) * (diagonal (dVec m⁻¹ n⁻¹) * (g : Matrix (Fin 4) (Fin 4) F) *
        diagonal (dVec m n)) * diagonal (dVec m⁻¹ n⁻¹)
      = (diagonal (dVec m n) * diagonal (dVec m⁻¹ n⁻¹)) * (g : Matrix (Fin 4) (Fin 4) F) *
          (diagonal (dVec m n) * diagonal (dVec m⁻¹ n⁻¹)) := by simp only [Matrix.mul_assoc]
    _ = (g : Matrix (Fin 4) (Fin 4) F) := by
        rw [diagonal_dVec_mul_inv hm hn, Matrix.one_mul, Matrix.mul_one]

end CFSG.ClassicalInvolution.Asc77.CX.MF2L
