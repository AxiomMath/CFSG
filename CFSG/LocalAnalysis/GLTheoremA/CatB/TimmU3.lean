module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.TimmU1

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Timm.UnitaryPoint

open Matrix CFSG.Open

variable {w : ℕ}

@[expose] noncomputable def liftM (B : Matrix (Fin w) (Fin w) F4) (d : F4) :
    Matrix (Fin (w + 2)) (Fin (w + 2)) F4 :=
  (Matrix.fromBlocks B 0 0 (d • (1 : Matrix (Fin 2) (Fin 2) F4))).submatrix
    finSumFinEquiv.symm finSumFinEquiv.symm

theorem liftM_WW (B : Matrix (Fin w) (Fin w) F4) (d : F4) (a b : Fin w) :
    liftM B d (Wc w a) (Wc w b) = B a b := by
  simp [liftM, finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₁₁]

theorem liftM_WT (B : Matrix (Fin w) (Fin w) F4) (d : F4) (a : Fin w) (t : Fin 2) :
    liftM B d (Wc w a) (Tp w t) = 0 := by
  simp [liftM, finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
    Matrix.fromBlocks_apply₁₂]

theorem liftM_TW (B : Matrix (Fin w) (Fin w) F4) (d : F4) (t : Fin 2) (b : Fin w) :
    liftM B d (Tp w t) (Wc w b) = 0 := by
  simp [liftM, finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
    Matrix.fromBlocks_apply₂₁]

theorem liftM_TT (B : Matrix (Fin w) (Fin w) F4) (d : F4) (s t : Fin 2) :
    liftM B d (Tp w s) (Tp w t) = d * (1 : Matrix (Fin 2) (Fin 2) F4) s t := by
  simp [liftM, finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₂]

theorem liftM_mulVec_e0 (B : Matrix (Fin w) (Fin w) F4) (d : F4) :
    liftM B d *ᵥ e0 w = d • e0 w := by
  funext k
  induction k using Fin.addCases with
  | left a =>
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    rw [Fin.sum_univ_add]
    simp [liftM_WT, e0_val_zero_of_castAdd]
  | right s =>
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    rw [Fin.sum_univ_add, Fin.sum_univ_two]
    simp only [liftM_TW, liftM_TT, zero_mul, Finset.sum_const_zero, zero_add, e0_natAdd_zero,
      e0_natAdd_one, mul_one, Finset.sum_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    fin_cases s <;> simp [e0_natAdd_zero, e0_natAdd_one, Matrix.one_apply]

theorem liftM_det (B : Matrix (Fin w) (Fin w) F4) (d : F4) :
    (liftM B d).det = B.det * d ^ 2 := by
  unfold liftM
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul,
    Matrix.det_one]
  simp

theorem rhoM_liftM (B : Matrix (Fin w) (Fin w) F4) (d : F4) : rhoM (liftM B d) = B := by
  ext a b
  simp [rhoM, liftM_WW]

theorem liftM_unitary {B : Matrix (Fin w) (Fin w) F4} (hB : IsUnitaryMat B) {d : F4}
    (hd : fr d * d = 1) : IsUnitaryMat (liftM B d) := by
  unfold IsUnitaryMat
  ext k m
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.one_apply]
  rw [Fin.sum_univ_add]
  have hBentry : ∀ i j : Fin w, ∑ a : Fin w, fr (B a i) * B a j = if i = j then 1 else 0 := by
    intro i j
    have := congrFun (congrFun hB i) j
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.one_apply] using this
  have hne : ∀ (i : Fin w) (t : Fin 2), (Fin.castAdd 2 i : Fin (w + 2)) ≠ Fin.natAdd w t := by
    intro i t h
    have := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    omega
  induction k using Fin.addCases with
  | left i =>
    induction m using Fin.addCases with
    | left j =>
      have h1 : ∑ a : Fin w, fr (liftM B d (Wc w a) (Wc w i)) * liftM B d (Wc w a) (Wc w j) =
          ∑ a : Fin w, fr (B a i) * B a j := by
        simp [liftM_WW]
      have h2 : ∑ t : Fin 2, fr (liftM B d (Tp w t) (Wc w i)) * liftM B d (Tp w t) (Wc w j) = 0 := by
        simp [liftM_TW]
      rw [h1, h2, add_zero, hBentry i j]
      simp [Fin.castAdd_inj]
    | right t =>
      have h1 : ∑ a : Fin w, fr (liftM B d (Wc w a) (Wc w i)) * liftM B d (Wc w a) (Tp w t) = 0 := by
        simp [liftM_WT]
      have h2 : ∑ u : Fin 2, fr (liftM B d (Tp w u) (Wc w i)) * liftM B d (Tp w u) (Tp w t) = 0 := by
        simp [liftM_TW]
      rw [h1, h2, add_zero, if_neg (hne i t)]
  | right s =>
    induction m using Fin.addCases with
    | left j =>
      have h1 : ∑ a : Fin w, fr (liftM B d (Wc w a) (Tp w s)) * liftM B d (Wc w a) (Wc w j) = 0 := by
        simp [liftM_WT]
      have h2 : ∑ u : Fin 2, fr (liftM B d (Tp w u) (Tp w s)) * liftM B d (Tp w u) (Wc w j) = 0 := by
        simp [liftM_TW]
      rw [h1, h2, zero_add, if_neg (fun h => hne j s h.symm)]
    | right t =>
      have h1 : ∑ a : Fin w, fr (liftM B d (Wc w a) (Tp w s)) * liftM B d (Wc w a) (Tp w t) = 0 := by
        simp [liftM_WT]
      have h2 : ∑ u : Fin 2, fr (liftM B d (Tp w u) (Tp w s)) * liftM B d (Tp w u) (Tp w t) =
          if s = t then 1 else 0 := by
        fin_cases s <;> fin_cases t <;>
          simp [Fin.sum_univ_two, liftM_TT, Matrix.one_apply, map_mul, hd, fr_fix01]
      rw [h1, h2, zero_add]
      simp [Fin.natAdd_inj]

theorem liftM_fr_det_mul_eq_one {B : Matrix (Fin w) (Fin w) F4} (hB : IsUnitaryMat B) :
    fr B.det * B.det = 1 := by
  rw [fr_apply]
  have h := det_pow_three_of_unitary hB
  calc B.det ^ 2 * B.det = B.det ^ 3 := by ring
    _ = 1 := h

theorem det_liftM_eq_one {B : Matrix (Fin w) (Fin w) F4} (hB : IsUnitaryMat B) :
    (liftM B B.det).det = 1 := by
  rw [liftM_det]
  have h := det_pow_three_of_unitary hB
  calc B.det * B.det ^ 2 = B.det ^ 3 := by ring
    _ = 1 := h

@[expose] noncomputable def liftGL (B : GL (Fin w) F4) (hB : IsUnitaryMat (B : Matrix (Fin w) (Fin w) F4)) :
    GL (Fin (w + 2)) F4 :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (liftM (B : Matrix (Fin w) (Fin w) F4)
    (B : Matrix (Fin w) (Fin w) F4).det) (by
      rw [det_liftM_eq_one hB]
      exact one_ne_zero)

theorem liftGL_val (B : GL (Fin w) F4) (hB : IsUnitaryMat (B : Matrix (Fin w) (Fin w) F4)) :
    ((liftGL B hB : GL (Fin (w + 2)) F4) : Matrix (Fin (w + 2)) (Fin (w + 2)) F4) =
      liftM (B : Matrix (Fin w) (Fin w) F4) (B : Matrix (Fin w) (Fin w) F4).det := by
  unfold liftGL
  rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]

theorem liftGL_mem (B : GL (Fin w) F4) (hB : IsUnitaryMat (B : Matrix (Fin w) (Fin w) F4)) :
    liftGL B hB ∈ stabSU w := by
  rw [mem_stabSU_iff, liftGL_val]
  refine ⟨det_liftM_eq_one hB, liftM_unitary hB (liftM_fr_det_mul_eq_one hB), ?_⟩
  exact ⟨_, liftM_mulVec_e0 _ _⟩

theorem rhoHom_surjective : Function.Surjective (rhoHom : ↥(stabSU w) →* ↥(unitSub w)) := by
  rintro ⟨B, hB⟩
  have hB' : IsUnitaryMat (B : Matrix (Fin w) (Fin w) F4) := hB
  refine ⟨⟨liftGL B hB', liftGL_mem B hB'⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  rw [rhoHom_val, rhoGL_val, liftGL_val, rhoM_liftM]

end CFSG.LocalAnalysis.GLTheoremA.Timm.UnitaryPoint

end
