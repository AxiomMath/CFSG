module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421SpDef

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K421SpProof

open Matrix K421CGProof K421LinProof

@[expose] def kapIdx : Idx ≃ Fin 3 ⊕ Fin 3 where
  toFun i := if i.2 = 0 then Sum.inl i.1 else Sum.inr i.1
  invFun := Sum.elim (fun j => (j, 0)) (fun j => (j, 1))
  left_inv := by
    rintro ⟨j, k⟩
    fin_cases k <;> simp
  right_inv := by
    rintro (j | j) <;> simp

theorem reindex_isometry_iff {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι']
    [DecidableEq ι'] {K : Type} [Field K] (κ : ι ≃ ι') (J h : Matrix ι ι K) :
    (Matrix.reindex κ κ h)ᵀ * Matrix.reindex κ κ J * Matrix.reindex κ κ h = Matrix.reindex κ κ J ↔
      hᵀ * J * h = J := by
  have e : (Matrix.reindex κ κ h)ᵀ * Matrix.reindex κ κ J * Matrix.reindex κ κ h =
      Matrix.reindex κ κ (hᵀ * J * h) := by
    simp only [Matrix.reindex_apply, Matrix.transpose_submatrix]
    rw [Matrix.submatrix_mul_equiv _ _ _ κ.symm _, Matrix.submatrix_mul_equiv _ _ _ κ.symm _]
  rw [e]
  exact (Matrix.reindex κ κ).apply_eq_iff_eq

theorem map_gramIsometry {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    {K : Type} [Field K] (κ : ι ≃ ι') (J : Matrix ι ι K) :
    (CFSG.Open.StatedAPI.gramIsometry J).map (reindexGL (R := K) κ).toMonoidHom =
      CFSG.Open.StatedAPI.gramIsometry (Matrix.reindex κ κ J) := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    have hh' : (h : Matrix ι ι K)ᵀ * J * (h : Matrix ι ι K) = J := hh
    show ((reindexGL (R := K) κ h : GL ι' K) : Matrix ι' ι' K)ᵀ * Matrix.reindex κ κ J *
      ((reindexGL (R := K) κ h : GL ι' K) : Matrix ι' ι' K) = Matrix.reindex κ κ J
    rw [reindexGL_val]
    exact (reindex_isometry_iff κ J _).2 hh'
  · intro hg
    refine ⟨(reindexGL (R := K) κ).symm g, ?_, (reindexGL (R := K) κ).apply_symm_apply g⟩
    have hgh : reindexGL (R := K) κ ((reindexGL (R := K) κ).symm g) = g :=
      (reindexGL (R := K) κ).apply_symm_apply g
    have hg' : (g : Matrix ι' ι' K)ᵀ * Matrix.reindex κ κ J * (g : Matrix ι' ι' K) =
        Matrix.reindex κ κ J := hg
    rw [← hgh, reindexGL_val] at hg'
    exact (reindex_isometry_iff κ J _).1 hg'

variable (F : Type) [Field F] [CharP F 2]

theorem reindex_JF : Matrix.reindex kapIdx kapIdx (JF F) =
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) := by
  have hneg : (-1 : F) = 1 := by
    have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
    linear_combination (-1 : F) * h2
  ext (i | i) (j | j)
  · simp [Matrix.reindex_apply, JF, bc, JI, kapIdx, Jm]
  · by_cases h : i = j
    · subst h
      simp [Matrix.reindex_apply, JF, bc, JI, kapIdx, Jm]
    · simp [Matrix.reindex_apply, JF, bc, JI, kapIdx, Jm, h]
  · by_cases h : i = j
    · subst h
      simp [Matrix.reindex_apply, JF, bc, JI, kapIdx, Jm, hneg]
    · simp [Matrix.reindex_apply, JF, bc, JI, kapIdx, Jm, h]
  · simp [Matrix.reindex_apply, JF, bc, JI, kapIdx, Jm]

theorem statedSp_eq_gramIsometry : CFSG.Open.StatedSp 3 F = CFSG.Open.StatedAPI.gramIsometry
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) := by
  ext A
  rw [CFSG.Open.StatedAPI.mem_statedSp_iff]
  rfl

@[expose] noncomputable def spIEquiv : ↥(SpI F) ≃* ↥(CFSG.Open.StatedSp 3 F) :=
  ((SpI F).equivMapOfInjective (reindexGL (R := F) kapIdx).toMonoidHom
    (reindexGL (R := F) kapIdx).injective).trans
    (MulEquiv.subgroupCongr (by
      rw [statedSp_eq_gramIsometry, ← reindex_JF]
      exact map_gramIsometry kapIdx (JF F)))

end K421SpProof

end CFSG.LocalAnalysis.RankThreeUC.S15
