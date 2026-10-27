module

public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap

variable {R : Type*} [CommRing R] {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R M₁]
  [AddCommGroup M₂] [Module R M₂] {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}

theorem map_autCongr_orthogonalGroup (e : Q₁.IsometryEquiv Q₂) :
    (TauCeti.QuadraticMap.orthogonalGroup Q₁).map
        (LinearEquiv.autCongr e.toLinearEquiv).toMonoidHom =
      TauCeti.QuadraticMap.orthogonalGroup Q₂ := by
  ext g
  constructor
  · rintro ⟨f, hf, rfl⟩
    refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 fun m => ?_
    rw [MulEquiv.coe_toMonoidHom, LinearEquiv.autCongr_apply_apply]
    erw [e.map_app, TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hf, ← e.map_app,
      e.apply_symm_apply]
  · intro hg
    refine ⟨(LinearEquiv.autCongr e.toLinearEquiv).symm g,
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 fun m => ?_,
      MulEquiv.apply_symm_apply _ _⟩
    rw [LinearEquiv.autCongr_symm_apply_apply]
    erw [← e.map_app, e.apply_symm_apply,
      TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg, e.map_app]

theorem map_autCongr_commutator_orthogonalGroup (e : Q₁.IsometryEquiv Q₂) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q₁,
        TauCeti.QuadraticMap.orthogonalGroup Q₁⁆.map
        (LinearEquiv.autCongr e.toLinearEquiv).toMonoidHom =
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q₂,
        TauCeti.QuadraticMap.orthogonalGroup Q₂⁆ := by
  rw [Subgroup.map_commutator, map_autCongr_orthogonalGroup]

@[expose] noncomputable def commutatorOrthogonalGroupCongr (e : Q₁.IsometryEquiv Q₂) :
    ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q₁,
        TauCeti.QuadraticMap.orthogonalGroup Q₁⁆ ≃*
      ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q₂,
        TauCeti.QuadraticMap.orthogonalGroup Q₂⁆ :=
  ((LinearEquiv.autCongr e.toLinearEquiv).subgroupMap _).trans
    (MulEquiv.subgroupCongr (by
      rw [← MulEquiv.toMonoidHom_eq_coe]
      exact map_autCongr_commutator_orthogonalGroup e))

@[simp]
theorem coe_commutatorOrthogonalGroupCongr_apply (e : Q₁.IsometryEquiv Q₂)
    (g : ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q₁,
      TauCeti.QuadraticMap.orthogonalGroup Q₁⁆) :
    ((commutatorOrthogonalGroupCongr e g :
        ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q₂,
          TauCeti.QuadraticMap.orthogonalGroup Q₂⁆) : M₂ ≃ₗ[R] M₂) =
      (e.toLinearEquiv.symm.trans (g : M₁ ≃ₗ[R] M₁)).trans e.toLinearEquiv := by
  rw [commutatorOrthogonalGroupCongr, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    MulEquiv.coe_subgroupMap_apply, LinearEquiv.autCongr_apply]

end CFSG.ClassicalGroups.Orthogonal
