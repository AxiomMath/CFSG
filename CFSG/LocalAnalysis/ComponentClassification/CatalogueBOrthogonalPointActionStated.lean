module

public import CFSG.ClassicalGroups.Orthogonal.Matrix
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionProjective

public section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointAction

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank

universe u v

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable (Q : QuadraticForm K V)

theorem orthogonal_projectivization_mk (g : TauCeti.QuadraticMap.orthogonalGroup Q)
    (x : V) (hx : x ≠ 0) :
    (g.val : V ≃ₗ[K] V) • Projectivization.mk K x hx =
      Projectivization.mk K (g.val x) (fun h => hx (g.val.map_eq_zero_iff.mp h)) := rfl

@[expose] noncomputable def orthogonalNativePointPerm
    (g : TauCeti.QuadraticMap.orthogonalGroup Q) : Equiv.Perm (singularLines Q) :=
  (MulAction.toPermHom (V ≃ₗ[K] V) (Projectivization K V) g.val).subtypePerm (by
      intro p
      induction p using Projectivization.ind with | h x hx => ?_
      change Q (g.val • Projectivization.mk K x hx).rep = 0 ↔
        Q (Projectivization.mk K x hx).rep = 0
      rw [orthogonal_projectivization_mk, map_rep_mk_eq_zero_iff,
        map_rep_mk_eq_zero_iff, map_of_mem g.property])

@[expose] noncomputable def orthogonalPointAction :
    TauCeti.QuadraticMap.orthogonalGroup Q →* Equiv.Perm (Points Q) :=
  (nativePointEquiv Q).permCongrHom.toMonoidHom.comp {
    toFun := orthogonalNativePointPerm Q
    map_one' := by
      apply Equiv.ext
      intro p
      apply Subtype.ext
      change (1 : V ≃ₗ[K] V) • p.val = p.val
      exact one_smul _ _
    map_mul' := by
      intro g h
      apply Equiv.ext
      intro p
      apply Subtype.ext
      change (g.val * h.val) • p.val = g.val • h.val • p.val
      exact mul_smul g.val h.val p.val }

theorem orthogonalPointAction_elementary (g : elementaryGroup Q) :
    orthogonalPointAction Q
      ⟨g.val, elementaryGroup_le_orthogonalGroup Q g.property⟩ = elementaryPointAction Q g := by
  apply Equiv.ext
  intro L
  apply (nativePointEquiv Q).symm.injective
  apply Subtype.ext
  rfl

theorem orthogonalPointAction_pointMk (g : TauCeti.QuadraticMap.orthogonalGroup Q)
    (x : V) (hx : x ≠ 0) (hQx : Q x = 0) :
    orthogonalPointAction Q g (pointMk x hx hQx) =
      pointMk ((g : V ≃ₗ[K] V) x)
        (fun h => hx ((g : V ≃ₗ[K] V).map_eq_zero_iff.mp h))
        (by rw [map_of_mem g.property, hQx]) := by
  rw [pointMk, pointMk]
  change (nativePointEquiv Q).permCongr (orthogonalNativePointPerm Q g)
    (nativePointEquiv Q (lineMk x hx hQx)) = _
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  apply congrArg (nativePointEquiv Q)
  apply Subtype.ext
  exact orthogonal_projectivization_mk Q g x hx

theorem orthogonalPointAction_submodule (g : TauCeti.QuadraticMap.orthogonalGroup Q)
    (L : Points Q) :
    (orthogonalPointAction Q g L).val = L.val.map ((g : V ≃ₗ[K] V) : V →ₗ[K] V) := by
  obtain ⟨x, hx, hQx, rfl⟩ := exists_eq_pointMk L
  rw [orthogonalPointAction_pointMk, pointMk_submodule, pointMk_submodule,
    Submodule.map_span, Set.image_singleton]
  rfl

section Matrices

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F]
variable {Q : QuadraticForm F (ι → F)} {Q₀ : (ι → F) → F}

@[expose] noncomputable def statedOrthogonalHom (hQ : ⇑Q = Q₀) :
    StatedOmega Q₀ →* TauCeti.QuadraticMap.orthogonalGroup Q where
  toFun g := ⟨toLinEquiv ι F g.val,
    Subgroup.commutator_le_self _ ((statedOmega_eq_comap hQ).le g.property)⟩
  map_one' := Subtype.ext (map_one (toLinEquiv ι F))
  map_mul' g h := Subtype.ext (map_mul (toLinEquiv ι F) g.val h.val)

@[expose] noncomputable def statedDerivedPointAction (hQ : ⇑Q = Q₀) :
    StatedOmega Q₀ →* Equiv.Perm (Points Q) :=
  (orthogonalPointAction Q).comp (statedOrthogonalHom hQ)

theorem statedScalar_le_actionKernel (hQ : ⇑Q = Q₀) :
    (StatedScalars ι F).subgroupOf (StatedOmega Q₀) ≤ (statedDerivedPointAction hQ).ker := by
  intro g hg
  have hscalar : toLinEquiv ι F g.val ∈ scalars F (ι → F) :=
    (mem_statedScalars_iff g.val).mp hg
  obtain ⟨a, ha⟩ := mem_scalars.mp hscalar
  rw [MonoidHom.mem_ker]
  apply Equiv.ext
  intro L
  obtain ⟨x, hx, hQx, rfl⟩ := exists_eq_pointMk L
  change orthogonalPointAction Q (statedOrthogonalHom hQ g) (pointMk x hx hQx) =
    pointMk x hx hQx
  rw [orthogonalPointAction_pointMk, pointMk_eq_iff]
  exact ⟨a, (ha x).symm⟩

@[expose] noncomputable def statedPointAction (hQ : ⇑Q = Q₀) :
    StatedProj (StatedOmega Q₀) →* Equiv.Perm (Points Q) :=
  QuotientGroup.lift _ (statedDerivedPointAction hQ) (statedScalar_le_actionKernel hQ)

theorem statedPointAction_mk_submodule (hQ : ⇑Q = Q₀)
    (g : StatedOmega Q₀) (L : Points Q) :
    (statedPointAction hQ (QuotientGroup.mk' _ g) L).val =
      L.val.map ((toLinEquiv ι F g.val) : (ι → F) →ₗ[F] (ι → F)) := by
  exact orthogonalPointAction_submodule Q (statedOrthogonalHom hQ g) L

theorem statedActionEquiv_scalarKernel (hQ : ⇑Q = Q₀)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) :
    ((StatedScalars ι F).subgroupOf (StatedOmega Q₀)).map
      (statedOmegaEquiv hQ hE).toMonoidHom = scalarKernel Q := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change (statedOmegaEquiv hQ hE y : (ι → F) ≃ₗ[F] (ι → F)) ∈ scalars F (ι → F)
    rw [coe_statedOmegaEquiv]
    exact (mem_statedScalars_iff y.val).mp hy
  · intro hx
    refine ⟨(statedOmegaEquiv hQ hE).symm x, ?_, by simp⟩
    apply (mem_statedScalars_iff _).mpr
    have h := coe_statedOmegaEquiv hQ hE ((statedOmegaEquiv hQ hE).symm x)
    rw [MulEquiv.apply_symm_apply] at h
    exact h ▸ hx

@[expose] noncomputable def statedActionEquiv (hQ : ⇑Q = Q₀)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) : StatedProj (StatedOmega Q₀) ≃* ProjectiveGroup Q :=
  QuotientGroup.congr _ _ (statedOmegaEquiv hQ hE) (statedActionEquiv_scalarKernel hQ hE)

theorem statedActionEquiv_mk (hQ : ⇑Q = Q₀)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) (g : StatedOmega Q₀) :
    statedActionEquiv hQ hE (g : StatedProj (StatedOmega Q₀)) =
      (statedOmegaEquiv hQ hE g : ProjectiveGroup Q) :=
  QuotientGroup.congr_mk _ _ _ _ g

theorem statedPointAction_equiv (hQ : ⇑Q = Q₀)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) (g : StatedProj (StatedOmega Q₀)) :
    statedPointAction hQ g = projectivePointAction Q (statedActionEquiv hQ hE g) := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective g
  have hs : statedPointAction hQ (a : StatedProj (StatedOmega Q₀)) =
      statedDerivedPointAction hQ a :=
    QuotientGroup.lift_mk _ (statedScalar_le_actionKernel hQ) a
  rw [statedActionEquiv_mk, hs]
  change _ = projectivePointAction Q
    (QuotientGroup.mk' (scalarKernel Q) (statedOmegaEquiv hQ hE a))
  rw [projectivePointAction_mk]
  change orthogonalPointAction Q (statedOrthogonalHom hQ a) = _
  rw [← orthogonalPointAction_elementary]
  congr 1

end Matrices

end CFSG.ComponentClassification.CatalogueBOrthogonalPointAction
