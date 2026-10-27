module

public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.ClassicalGroups.Orthogonal

open Matrix CFSG.Assembly.LowTwoRank

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

variable (ι K) in
@[expose] noncomputable def toLinEquiv : GL ι K ≃* ((ι → K) ≃ₗ[K] (ι → K)) :=
  Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv K (ι → K))

@[simp]
theorem toLinEquiv_apply (A : GL ι K) (v : ι → K) :
    toLinEquiv ι K A v = (A : Matrix ι ι K) *ᵥ v :=
  rfl

theorem closure_isometries_eq_comap {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K}
    (hQ : ⇑Q = Q₀) :
    Subgroup.closure {A : GL ι K | ∀ v, Q₀ ((A : Matrix ι ι K) *ᵥ v) = Q₀ v} =
      (TauCeti.QuadraticMap.orthogonalGroup Q).comap (toLinEquiv ι K).toMonoidHom := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro A hA
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
    rw [MulEquiv.coe_toMonoidHom, toLinEquiv_apply, hQ]
    exact hA v
  · intro A hA
    apply Subgroup.subset_closure
    intro v
    have := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (Subgroup.mem_comap.mp hA) v
    rwa [MulEquiv.coe_toMonoidHom, toLinEquiv_apply, hQ] at this

theorem statedOmega_eq_comap {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀) :
    StatedOmega Q₀ =
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆.comap
        (toLinEquiv ι K).toMonoidHom := by
  have key : ∀ H : Subgroup ((ι → K) ≃ₗ[K] (ι → K)),
      H.comap (toLinEquiv ι K).toMonoidHom = H.map (toLinEquiv ι K).symm.toMonoidHom :=
    fun H => Subgroup.comap_equiv_eq_map_symm (toLinEquiv ι K) H
  rw [StatedOmega, closure_isometries_eq_comap hQ, key, key, Subgroup.map_commutator]

theorem statedOmega_eq_map_elementaryGroup {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K}
    (hQ : ⇑Q = Q₀)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) :
    StatedOmega Q₀ = (elementaryGroup Q).map (toLinEquiv ι K).symm.toMonoidHom := by
  rw [statedOmega_eq_comap hQ, hE]
  exact Subgroup.comap_equiv_eq_map_symm (toLinEquiv ι K) _

theorem mem_statedScalars_iff (A : GL ι K) :
    A ∈ StatedScalars ι K ↔ toLinEquiv ι K A ∈ scalars K (ι → K) := by
  constructor
  · rintro ⟨u, rfl⟩
    refine mem_scalars.mpr ⟨u, fun v => ?_⟩
    rw [toLinEquiv_apply, Matrix.GeneralLinearGroup.coe_scalar]
    ext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  · intro h
    obtain ⟨c, hc⟩ := mem_scalars.mp h
    rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
    · refine ⟨1, Units.ext (Matrix.ext fun i => isEmptyElim i)⟩
    · have hc0 : c ≠ 0 := by
        rintro rfl
        have := hc (Pi.single i₀ 1)
        rw [zero_smul, LinearEquiv.map_eq_zero_iff, Pi.single_eq_zero_iff] at this
        exact one_ne_zero this
      refine ⟨Units.mk0 c hc0, Units.ext (Matrix.ext_of_mulVec_single fun k => ?_)⟩
      rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
      have := hc (Pi.single k 1)
      rw [toLinEquiv_apply] at this
      rw [this]
      ext i
      simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

section Proj

variable {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K}

@[expose] noncomputable def statedOmegaEquiv (hQ : ⇑Q = Q₀)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) :
    StatedOmega Q₀ ≃* elementaryGroup Q :=
  ((toLinEquiv ι K).subgroupMap (StatedOmega Q₀)).trans (MulEquiv.subgroupCongr (by
    rw [statedOmega_eq_comap hQ, hE]
    exact Subgroup.map_comap_eq_self_of_surjective (toLinEquiv ι K).surjective _))

theorem coe_statedOmegaEquiv (hQ : ⇑Q = Q₀)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) (A : StatedOmega Q₀) :
    (statedOmegaEquiv hQ hE A : (ι → K) ≃ₗ[K] (ι → K)) = toLinEquiv ι K A :=
  rfl

noncomputable def statedProjEquiv (hQ : ⇑Q = Q₀)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) :
    StatedProj (StatedOmega Q₀) ≃* ProjElementary Q :=
  QuotientGroup.congr _ _ (statedOmegaEquiv hQ hE) (by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, mem_statedScalars_iff] at hy
      rw [Subgroup.mem_subgroupOf]
      change ((statedOmegaEquiv hQ hE y : elementaryGroup Q) : (ι → K) ≃ₗ[K] (ι → K)) ∈
        scalars K (ι → K)
      rw [coe_statedOmegaEquiv]
      exact hy
    · intro hx
      refine ⟨(statedOmegaEquiv hQ hE).symm x, ?_, by simp⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, mem_statedScalars_iff]
      rw [Subgroup.mem_subgroupOf] at hx
      have h1 : (statedOmegaEquiv hQ hE ((statedOmegaEquiv hQ hE).symm x) :
          (ι → K) ≃ₗ[K] (ι → K)) = x := by rw [MulEquiv.apply_symm_apply]
      rw [coe_statedOmegaEquiv] at h1
      rw [h1]
      exact hx)

theorem isSimpleGroup_statedProj_of_eq (hQ : ⇑Q = Q₀)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) [IsSimpleGroup (ProjElementary Q)] :
    IsSimpleGroup (StatedProj (StatedOmega Q₀)) :=
  (statedProjEquiv hQ hE).isSimpleGroup

end Proj

end CFSG.ClassicalGroups.Orthogonal
