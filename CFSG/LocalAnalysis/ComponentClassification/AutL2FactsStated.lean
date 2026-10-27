module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsTransport

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo Subgroup
open CFSG.Assembly.LowTwoRank (StatedSL StatedProj specialLinearGroupEquivStatedSL
  projectiveSpecialLinearGroupEquivStatedProj statedSL_eq_range_toGL)

universe u v

variable {F₁ : Type} [Field F₁] {F : Type} [Field F]

@[expose] def statedEquiv (θ : F₁ ≃+* F) : StatedProj (StatedSL 2 F₁) ≃* PSL2 F :=
  (projectiveSpecialLinearGroupEquivStatedProj 2 F₁).symm.trans (psl2RingEquiv θ)

theorem toPGL_statedEquiv_mk (θ : F₁ ≃+* F) (M : StatedSL 2 F₁) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL (statedEquiv θ (QuotientGroup.mk M)) =
      Matrix.ProjGenLinGroup.mk
        (Matrix.GeneralLinearGroup.map θ.toRingHom (M : GL (Fin 2) F₁)) := by
  obtain ⟨M₁, rfl⟩ := (specialLinearGroupEquivStatedSL 2 F₁).surjective M
  have h1 : (projectiveSpecialLinearGroupEquivStatedProj 2 F₁).symm
      (QuotientGroup.mk (specialLinearGroupEquivStatedSL 2 F₁ M₁)) =
      QuotientGroup.mk' (Subgroup.center _) M₁ := by
    apply (projectiveSpecialLinearGroupEquivStatedProj 2 F₁).injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  rw [statedEquiv, MulEquiv.trans_apply, h1, psl2RingEquiv_mk]
  change Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL _) = _
  congr 1
  ext i j
  rfl

theorem statedEquiv_mk_surjective (θ : F₁ ≃+* F) (x : PSL2 F) :
    ∃ M : StatedSL 2 F₁, statedEquiv θ (QuotientGroup.mk M) = x := by
  obtain ⟨y, rfl⟩ := (statedEquiv θ).surjective x
  obtain ⟨M, rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨M, rfl⟩

theorem mem_statedSL_iff (A : GL (Fin 2) F₁) :
    A ∈ StatedSL 2 F₁ ↔ (A : Matrix (Fin 2) (Fin 2) F₁).det = 1 :=
  CFSG.Open.StatedAPI.mem_statedSL_iff

theorem conj_mem_statedSL (A : GL (Fin 2) F₁) (M : StatedSL 2 F₁) :
    A * (M : GL (Fin 2) F₁) * A⁻¹ ∈ StatedSL 2 F₁ := by
  rw [mem_statedSL_iff]
  have hM := (mem_statedSL_iff _).mp M.2
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, hM, mul_one]
  rw [← Matrix.det_mul, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel]
  simp

theorem det_map_gl (σ : F₁ ≃+* F₁) (M : GL (Fin 2) F₁) :
    ((Matrix.GeneralLinearGroup.map σ.toRingHom M : GL (Fin 2) F₁) :
      Matrix (Fin 2) (Fin 2) F₁).det = σ (M : Matrix (Fin 2) (Fin 2) F₁).det := by
  have : σ (M : Matrix (Fin 2) (Fin 2) F₁).det =
      (σ.toRingHom.mapMatrix (M : Matrix (Fin 2) (Fin 2) F₁)).det :=
    RingHom.map_det σ.toRingHom _
  rw [this]
  rfl

theorem map_mem_statedSL (σ : F₁ ≃+* F₁) (M : StatedSL 2 F₁) :
    Matrix.GeneralLinearGroup.map σ.toRingHom (M : GL (Fin 2) F₁) ∈ StatedSL 2 F₁ := by
  rw [mem_statedSL_iff, det_map_gl, (mem_statedSL_iff _).mp M.2, map_one]

theorem congr_statedEquiv_conj (θ : F₁ ≃+* F) (A : GL (Fin 2) F₁)
    (φ : MulAut (StatedProj (StatedSL 2 F₁)))
    (hφ : ∀ M N : StatedSL 2 F₁, (N : GL (Fin 2) F₁) = A * M * A⁻¹ →
      φ (QuotientGroup.mk M) = QuotientGroup.mk N) :
    MulAut.congr (statedEquiv θ) φ =
      pglAction F (Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map θ.toRingHom A)) := by
  ext x
  obtain ⟨M, rfl⟩ := statedEquiv_mk_surjective θ x
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    hφ M ⟨_, conj_mem_statedSL A M⟩ rfl, toPGL_statedEquiv_mk, toPGL_pglAction,
    toPGL_statedEquiv_mk]
  simp only [map_mul, map_inv]

theorem congr_statedEquiv_field (θ : F₁ ≃+* F) (σ₁ : F₁ ≃+* F₁)
    (φ : MulAut (StatedProj (StatedSL 2 F₁)))
    (hφ : ∀ M N : StatedSL 2 F₁,
      (N : GL (Fin 2) F₁) = Matrix.GeneralLinearGroup.map σ₁.toRingHom (M : GL (Fin 2) F₁) →
      φ (QuotientGroup.mk M) = QuotientGroup.mk N) :
    MulAut.congr (statedEquiv θ) φ = psl2FieldAut F (θ.symm.trans (σ₁.trans θ)) := by
  ext x
  obtain ⟨M, rfl⟩ := statedEquiv_mk_surjective θ x
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    hφ M ⟨_, map_mem_statedSL σ₁ M⟩ rfl, toPGL_statedEquiv_mk, psl2FieldAut_toPGL,
    toPGL_statedEquiv_mk, pgl2FieldAut_apply]
  change _ = pgl2RingEquiv _ (QuotientGroup.mk' (Subgroup.center _) _)
  rw [pgl2RingEquiv_mk]
  change Matrix.ProjGenLinGroup.mk _ = Matrix.ProjGenLinGroup.mk _
  congr 1
  ext i j
  simp [Matrix.GeneralLinearGroup.map]

variable [Finite F]

theorem autEquiv_eq_conj {Y : Type*} [Group Y] (e e₂ : Y ≃* PSL2 F) (α : MulAut Y) :
    autEquiv e α = (semilinearEquivAut F).symm (e₂.symm.trans e) * autEquiv e₂ α *
      ((semilinearEquivAut F).symm (e₂.symm.trans e))⁻¹ := by
  rw [autEquiv_eq_iff]
  change MulAut.congr e α = semilinearEquivAut F _
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  change MulAut.congr e α = (e₂.symm.trans e) * semilinearAction F (autEquiv e₂ α) *
    (e₂.symm.trans e)⁻¹
  rw [semilinearAction_autEquiv]
  ext x
  simp [MulAut.congr_apply]

end CFSG.ComponentClassification.AutL2Facts

namespace CFSG.GorensteinWalter
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo

variable {F F' : Type} [Field F] [Field F']

theorem toPGL_psl2RingEquiv (σ : F ≃+* F') (x : PSL2 F) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL
        (CFSG.GorensteinWalter.psl2RingEquiv σ x) =
      CFSG.GorensteinWalter.pgl2RingEquiv σ
        (Matrix.ProjectiveSpecialLinearGroup.toPGL x) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  change Matrix.ProjectiveSpecialLinearGroup.toPGL
      (CFSG.GorensteinWalter.psl2RingEquiv σ
        (QuotientGroup.mk' (Subgroup.center
          (Matrix.SpecialLinearGroup (Fin 2) F)) g)) =
    CFSG.GorensteinWalter.pgl2RingEquiv σ
      (Matrix.ProjectiveSpecialLinearGroup.toPGL
        (QuotientGroup.mk' (Subgroup.center
          (Matrix.SpecialLinearGroup (Fin 2) F)) g))
  rw [CFSG.GorensteinWalter.psl2RingEquiv_mk]
  simp only [QuotientGroup.mk'_apply]
  rw [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk]
  rw [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk]
  rw [show Matrix.ProjGenLinGroup.mk
      (Matrix.SpecialLinearGroup.toGL
        ((Matrix.SpecialLinearGroup.map σ.toRingHom) g)) =
      QuotientGroup.mk' (Subgroup.center
        (Matrix.GeneralLinearGroup (Fin 2) F'))
        (Matrix.SpecialLinearGroup.toGL
          ((Matrix.SpecialLinearGroup.map σ.toRingHom) g)) from rfl]
  rw [show Matrix.ProjGenLinGroup.mk
      (Matrix.SpecialLinearGroup.toGL g) =
      QuotientGroup.mk' (Subgroup.center
        (Matrix.GeneralLinearGroup (Fin 2) F))
        (Matrix.SpecialLinearGroup.toGL g) from rfl]
  rw [CFSG.GorensteinWalter.pgl2RingEquiv_mk]
  have hmat : Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map σ.toRingHom) g) =
      Matrix.GeneralLinearGroup.map σ.toRingHom
        (Matrix.SpecialLinearGroup.toGL g) := by
    apply Units.ext
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe,
      Matrix.GeneralLinearGroup.map_apply]
  rw [hmat]

theorem psl2RingEquiv_pglAction (σ : F ≃+* F') (g : PGL2 F) :
    MulAut.congr (CFSG.GorensteinWalter.psl2RingEquiv σ) (pglAction F g) =
      pglAction F' (CFSG.GorensteinWalter.pgl2RingEquiv σ g) := by
  ext x
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  change Matrix.ProjectiveSpecialLinearGroup.toPGL
      (CFSG.GorensteinWalter.psl2RingEquiv σ
        (pglAction F g ((CFSG.GorensteinWalter.psl2RingEquiv σ).symm x))) =
    Matrix.ProjectiveSpecialLinearGroup.toPGL
      (pglAction F' (CFSG.GorensteinWalter.pgl2RingEquiv σ g) x)
  have hsymm : Matrix.ProjectiveSpecialLinearGroup.toPGL
      ((CFSG.GorensteinWalter.psl2RingEquiv σ).symm x) =
      (CFSG.GorensteinWalter.pgl2RingEquiv σ).symm
        (Matrix.ProjectiveSpecialLinearGroup.toPGL x) := by
    apply (CFSG.GorensteinWalter.pgl2RingEquiv σ).injective
    rw [MulEquiv.apply_symm_apply, ← toPGL_psl2RingEquiv σ
      ((CFSG.GorensteinWalter.psl2RingEquiv σ).symm x),
      MulEquiv.apply_symm_apply]
  rw [toPGL_psl2RingEquiv, toPGL_pglAction, toPGL_pglAction, hsymm]
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]

end CFSG.GorensteinWalter
