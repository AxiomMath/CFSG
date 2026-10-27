module

public import CFSG.ClassicalGroups.Orthogonal.Eichler

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

universe u v w

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {W : Type w} [AddCommGroup W] [Module K W]
variable {Q : QuadraticForm K V} {R : QuadraticForm K W}

theorem polar_isometry (e : Q.IsometryEquiv R) (x y : V) :
    polar R (e x) (e y) = polar Q x y := e.polar_apply x y

theorem eichlerLin_isometry_apply (e : Q.IsometryEquiv R) (a b x : V) :
    e (eichlerLin Q a b x) = eichlerLin R (e a) (e b) (e x) := by
  rw [eichlerLin_apply, eichlerLin_apply, map_sub, map_add, map_smul, map_smul,
    polar_isometry, polar_isometry, e.map_app]

theorem eichler_isometry_apply (e : Q.IsometryEquiv R) (a b x : V) :
    e (eichler Q a b x) = eichler R (e a) (e b) (e x) := by
  by_cases h : Q a = 0 ∧ polar Q a b = 0
  · have hR : R (e a) = 0 ∧ polar R (e a) (e b) = 0 := by
      rwa [e.map_app, polar_isometry]
    rw [eichler_apply h.1 h.2, eichler_apply hR.1 hR.2, map_sub, map_add,
      map_smul, map_smul, polar_isometry, polar_isometry, e.map_app]
  · have hR : ¬(R (e a) = 0 ∧ polar R (e a) (e b) = 0) := by
      rwa [e.map_app, polar_isometry]
    rw [eichler_of_not h, eichler_of_not hR]
    rfl

theorem eichler_isometry (e : Q.IsometryEquiv R) (a b : V) :
    LinearEquiv.autCongr e.toLinearEquiv (eichler Q a b) =
      eichler R (e a) (e b) := by
  apply LinearEquiv.ext
  intro x
  rw [LinearEquiv.autCongr_apply_apply]
  change e (eichler Q a b (e.symm x)) = eichler R (e a) (e b) x
  rw [eichler_isometry_apply, e.apply_symm_apply]

theorem eichler_isometry_symm (e : Q.IsometryEquiv R) (a b : W) :
    (LinearEquiv.autCongr e.toLinearEquiv).symm (eichler R a b) =
      eichler Q (e.symm a) (e.symm b) := by
  apply (LinearEquiv.autCongr e.toLinearEquiv).injective
  rw [MulEquiv.apply_symm_apply, eichler_isometry, e.apply_symm_apply, e.apply_symm_apply]

theorem eichler_isometry_inverse_apply (e : Q.IsometryEquiv R) (a b : V) (x : W) :
    e.symm (eichler R (e a) (e b) x) = eichler Q a b (e.symm x) := by
  apply e.injective
  change e (e.symm (eichler R (e a) (e b) x)) = e (eichler Q a b (e.symm x))
  rw [e.apply_symm_apply, eichler_isometry_apply, e.apply_symm_apply]

private theorem elementaryGroup_map_le (e : Q.IsometryEquiv R) :
    (elementaryGroup Q).map (LinearEquiv.autCongr e.toLinearEquiv).toMonoidHom ≤
      elementaryGroup R := by
  apply Subgroup.map_le_iff_le_comap.mpr
  apply elementaryGroup_le_of_eichler_mem
  intro a b _ _
  change LinearEquiv.autCongr e.toLinearEquiv (eichler Q a b) ∈ elementaryGroup R
  rw [eichler_isometry]
  exact eichler_mem_elementaryGroup R (e a) (e b)

theorem elementaryGroup_map (e : Q.IsometryEquiv R) :
    (elementaryGroup Q).map (LinearEquiv.autCongr e.toLinearEquiv).toMonoidHom =
      elementaryGroup R := by
  apply le_antisymm (elementaryGroup_map_le e)
  apply elementaryGroup_le_of_eichler_mem
  intro a b _ _
  refine ⟨eichler Q (e.symm a) (e.symm b), eichler_mem_elementaryGroup Q _ _, ?_⟩
  change LinearEquiv.autCongr e.toLinearEquiv (eichler Q (e.symm a) (e.symm b)) = _
  rw [eichler_isometry, e.apply_symm_apply, e.apply_symm_apply]

@[expose] def elementaryIsometryEquiv (e : Q.IsometryEquiv R) :
    elementaryGroup Q ≃* elementaryGroup R :=
  ((LinearEquiv.autCongr e.toLinearEquiv).subgroupMap (elementaryGroup Q)).trans
    (MulEquiv.subgroupCongr (elementaryGroup_map e))

theorem elementaryIsometryEquiv_val (e : Q.IsometryEquiv R) (g : elementaryGroup Q) :
    (elementaryIsometryEquiv e g).val = LinearEquiv.autCongr e.toLinearEquiv g.val := rfl

theorem elementaryIsometryEquiv_apply (e : Q.IsometryEquiv R)
    (g : elementaryGroup Q) (x : W) :
    (elementaryIsometryEquiv e g).val x = e (g.val (e.symm x)) :=
  LinearEquiv.autCongr_apply_apply e.toLinearEquiv g.val x

theorem elementaryIsometryEquiv_symm_apply (e : Q.IsometryEquiv R)
    (g : elementaryGroup R) (x : V) :
    ((elementaryIsometryEquiv e).symm g).val x = e.symm (g.val (e x)) := by
  exact LinearEquiv.autCongr_symm_apply_apply e.toLinearEquiv g.val x

end CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry
