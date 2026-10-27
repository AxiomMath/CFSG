module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointIsometryBasic
public import Mathlib.Tactic.Positivity.Finset

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

universe u v w

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {W : Type w} [AddCommGroup W] [Module K W]
variable {Q : QuadraticForm K V} {R : QuadraticForm K W}

theorem polar_nondegenerate_isometry (e : Q.IsometryEquiv R)
    (hQ : Q.polarBilin.Nondegenerate) : R.polarBilin.Nondegenerate := by
  constructor
  · intro y hy
    have hx : e.symm y = 0 := hQ.1 (e.symm y) (by
      intro x
      change polar Q (e.symm y) x = 0
      rw [← polar_isometry e, e.apply_symm_apply]
      exact hy (e x))
    exact e.symm.toLinearEquiv.map_eq_zero_iff.mp hx
  · intro y hy
    have hx : e.symm y = 0 := hQ.2 (e.symm y) (by
      intro x
      change polar Q x (e.symm y) = 0
      rw [← polar_isometry e, e.apply_symm_apply]
      exact hy (e x))
    exact e.symm.toLinearEquiv.map_eq_zero_iff.mp hx

theorem polar_nondegenerate_isometry_iff (e : Q.IsometryEquiv R) :
    R.polarBilin.Nondegenerate ↔ Q.polarBilin.Nondegenerate :=
  ⟨polar_nondegenerate_isometry e.symm, polar_nondegenerate_isometry e⟩

theorem submodule_finrank_isometry (e : Q.IsometryEquiv R) (T : Submodule K V) :
    Module.finrank K (T.map e.toLinearMap) = Module.finrank K T :=
  e.toLinearEquiv.finrank_map_eq T

theorem submodule_singular_isometry (e : Q.IsometryEquiv R) (T : Submodule K V)
    (hT : ∀ x ∈ T, Q x = 0) : ∀ y ∈ T.map e.toLinearMap, R y = 0 := by
  rintro y ⟨x, hx, rfl⟩
  exact (e.map_app x).trans (hT x hx)

theorem singular_three_isometry (e : Q.IsometryEquiv R)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    ∃ T : Submodule K W, Module.finrank K T = 3 ∧ ∀ x ∈ T, R x = 0 := by
  obtain ⟨T, hT3, hTs⟩ := hT
  exact ⟨T.map e.toLinearMap, (submodule_finrank_isometry e T).trans hT3,
    submodule_singular_isometry e T hTs⟩

theorem singular_three_isometry_iff (e : Q.IsometryEquiv R) :
    (∃ T : Submodule K W, Module.finrank K T = 3 ∧ ∀ x ∈ T, R x = 0) ↔
      ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0 :=
  ⟨singular_three_isometry e.symm, singular_three_isometry e⟩

theorem orthogonalGroupCongr_apply (e : Q.IsometryEquiv R)
    (g : TauCeti.QuadraticMap.orthogonalGroup Q) (x : W) :
    (TauCeti.QuadraticMap.orthogonalGroupCongr e g).val x = e (g.val (e.symm x)) :=
  TauCeti.QuadraticMap.coe_orthogonalGroupCongr_apply e g x

theorem orthogonalGroupCongr_symm_apply (e : Q.IsometryEquiv R)
    (g : TauCeti.QuadraticMap.orthogonalGroup R) (x : V) :
    ((TauCeti.QuadraticMap.orthogonalGroupCongr e).symm g).val x = e.symm (g.val (e x)) :=
  TauCeti.QuadraticMap.coe_orthogonalGroupCongr_symm_apply e g x

theorem orthogonalGroupCongr_val (e : Q.IsometryEquiv R)
    (g : TauCeti.QuadraticMap.orthogonalGroup Q) :
    (TauCeti.QuadraticMap.orthogonalGroupCongr e g).val =
      LinearEquiv.autCongr e.toLinearEquiv g.val := by
  apply LinearEquiv.ext
  intro x
  exact (orthogonalGroupCongr_apply e g x).trans
    (LinearEquiv.autCongr_apply_apply e.toLinearEquiv g.val x).symm

theorem orthogonalGroup_map_isometry (e : Q.IsometryEquiv R) :
    (TauCeti.QuadraticMap.orthogonalGroup Q).map
        (LinearEquiv.autCongr e.toLinearEquiv).toMonoidHom =
      TauCeti.QuadraticMap.orthogonalGroup R := by
  ext g
  constructor
  · rintro ⟨f, hf, rfl⟩
    have h := (TauCeti.QuadraticMap.orthogonalGroupCongr e ⟨f, hf⟩).property
    rwa [orthogonalGroupCongr_val] at h
  · intro hg
    let f := (TauCeti.QuadraticMap.orthogonalGroupCongr e).symm ⟨g, hg⟩
    refine ⟨f.val, f.property, ?_⟩
    calc
      LinearEquiv.autCongr e.toLinearEquiv f.val =
          (TauCeti.QuadraticMap.orthogonalGroupCongr e f).val :=
        (orthogonalGroupCongr_val e f).symm
      _ = g := congrArg Subtype.val
        ((TauCeti.QuadraticMap.orthogonalGroupCongr e).apply_symm_apply ⟨g, hg⟩)

theorem derivedOrthogonal_map_isometry (e : Q.IsometryEquiv R) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆.map
        (LinearEquiv.autCongr e.toLinearEquiv).toMonoidHom =
      ⁅TauCeti.QuadraticMap.orthogonalGroup R, TauCeti.QuadraticMap.orthogonalGroup R⁆ := by
  rw [Subgroup.map_commutator, orthogonalGroup_map_isometry]

theorem derived_eq_elementary_isometry (e : Q.IsometryEquiv R)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup R, TauCeti.QuadraticMap.orthogonalGroup R⁆ =
      elementaryGroup R := by
  rw [← derivedOrthogonal_map_isometry e, hE, elementaryGroup_map]

theorem derived_eq_elementary_isometry_iff (e : Q.IsometryEquiv R) :
    (⁅TauCeti.QuadraticMap.orthogonalGroup R, TauCeti.QuadraticMap.orthogonalGroup R⁆ =
      elementaryGroup R) ↔
    (⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) :=
  ⟨derived_eq_elementary_isometry e.symm, derived_eq_elementary_isometry e⟩

end CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry
