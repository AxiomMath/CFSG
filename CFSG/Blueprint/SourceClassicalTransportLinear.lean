module

public import CFSG.Blueprint.SourceClassicalModels
public import CFSG.Open.StatedAPI

public noncomputable section

namespace CFSG.Blueprint.EvenSource

open CFSG.Assembly.LowTwoRank Module Matrix

@[expose] def quotientInfCongr {G₁ G₂ : Type*} [Group G₁] [Group G₂] (Φ : G₁ ≃* G₂)
    {H₁ S₁ : Subgroup G₁} {H₂ S₂ : Subgroup G₂} [S₁.Normal] [S₂.Normal]
    (hH : H₁.map Φ.toMonoidHom = H₂) (hS : S₁.map Φ.toMonoidHom = S₂) :
    H₁ ⧸ S₁.subgroupOf H₁ ≃* H₂ ⧸ S₂.subgroupOf H₂ := by
  let E : H₁ ≃* H₂ :=
    (H₁.equivMapOfInjective Φ.toMonoidHom Φ.injective).trans (MulEquiv.subgroupCongr hH)
  refine QuotientGroup.congr _ _ E ?_
  ext x
  obtain ⟨h, rfl⟩ := E.surjective x
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨h', hh', hEq⟩
    have hh : h' = h := E.injective hEq
    subst hh
    have : Φ h' ∈ S₁.map Φ.toMonoidHom := ⟨h', hh', rfl⟩
    rw [hS] at this
    exact this
  · intro hx
    refine ⟨h, ?_, rfl⟩
    have hx' : Φ (h : G₁) ∈ S₂ := hx
    rw [← hS] at hx'
    obtain ⟨g, hg, hgh⟩ := hx'
    rwa [Φ.injective hgh] at hg

section Basis

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {ι : Type} [Fintype ι]
  [DecidableEq ι]

@[expose] def sourceGLEquiv (b : Basis ι K V) : LinearMap.GeneralLinearGroup K V ≃* GL ι K :=
  Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv

theorem coe_sourceGLEquiv (b : Basis ι K V) (g : LinearMap.GeneralLinearGroup K V) :
    ((sourceGLEquiv b g : GL ι K) : Matrix ι ι K) =
      LinearMap.toMatrix b b (g : Module.End K V) :=
  rfl

theorem coe_sourceGLEquiv_symm (b : Basis ι K V) (A : GL ι K) :
    (((sourceGLEquiv b).symm A : LinearMap.GeneralLinearGroup K V) : Module.End K V) =
      Matrix.toLin b b (A : Matrix ι ι K) :=
  rfl

theorem map_sourceScalars_sourceGLEquiv (b : Basis ι K V) :
    (sourceScalars K V).map (sourceGLEquiv b).toMonoidHom = StatedScalars ι K := by
  rw [sourceScalars, StatedScalars, MonoidHom.map_range]
  congr 1
  refine MonoidHom.ext fun c => Units.ext ?_
  change LinearMap.toMatrixAlgEquiv b (algebraMap K (Module.End K V) c) =
    ((GeneralLinearGroup.scalar ι c : GL ι K) : Matrix ι ι K)
  rw [AlgEquiv.commutes, GeneralLinearGroup.coe_scalar, Matrix.algebraMap_eq_diagonal]
  rfl

theorem map_sourceSL_sourceGLEquiv (b : Basis ι K V) :
    (sourceSL K V).map (sourceGLEquiv b).toMonoidHom =
      (GeneralLinearGroup.det : GL ι K →* Kˣ).ker := by
  ext A
  rw [Subgroup.mem_map_equiv, sourceSL, MonoidHom.mem_ker, MonoidHom.mem_ker, Units.ext_iff,
    GeneralLinearGroup.val_det_apply, Units.val_one]
  change LinearMap.det (Matrix.toLin b b (A : Matrix ι ι K)) = 1 ↔ _
  rw [LinearMap.det_toLin]

end Basis

export CFSG.Open.StatedAPI (statedSL_eq_ker_det)

theorem sourceClassicalModel_of_stated_PSL {X : Type} [Group X] {n p f : ℕ}
    (h : StatedClassicalModel X .PSL n p f) : SourceClassicalModel X .PSL n p f := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := h
  refine ⟨hadm, K, inferInstance, inferInstance, Fin n → K, inferInstance, inferInstance,
    inferInstance, sourceSL K (Fin n → K), ⟨e.trans (quotientInfCongr
      (sourceGLEquiv (Pi.basisFun K (Fin n))).symm ?_ ?_)⟩, hK, Module.finrank_fin_fun K, rfl⟩
  · rw [statedSL_eq_ker_det, ← map_sourceSL_sourceGLEquiv (Pi.basisFun K (Fin n)),
      Subgroup.map_map]
    simp
  · rw [← map_sourceScalars_sourceGLEquiv (Pi.basisFun K (Fin n)), Subgroup.map_map]
    simp

theorem stated_of_sourceClassicalModel_PSL {X : Type} [Group X] {n p f : ℕ}
    (h : SourceClassicalModel X .PSL n p f) : StatedClassicalModel X .PSL n p f := by
  obtain ⟨hadm, K, _, _, V, _, _, _, H, ⟨e⟩, hK, hV, rfl⟩ := h
  let b := Module.finBasisOfFinrankEq K V hV
  exact ⟨hadm, K, inferInstance, inferInstance, hK, ⟨e.trans (quotientInfCongr (sourceGLEquiv b)
    (by rw [map_sourceSL_sourceGLEquiv, statedSL_eq_ker_det]) (map_sourceScalars_sourceGLEquiv b))⟩⟩

end CFSG.Blueprint.EvenSource
