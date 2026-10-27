module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointIsometryPoints
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionProjective

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CatalogueBOrthogonalPointAction

universe u v w

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {W : Type w} [AddCommGroup W] [Module K W]
variable {Q : QuadraticForm K V} {R : QuadraticForm K W}

theorem mem_scalarKernel_isometry_iff (e : Q.IsometryEquiv R) (g : elementaryGroup Q) :
    elementaryIsometryEquiv e g ∈ scalarKernel R ↔ g ∈ scalarKernel Q := by
  rw [mem_scalarKernel_iff_units R, mem_scalarKernel_iff_units Q]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, fun x => ?_⟩
    have h := ha (e x)
    change (elementaryIsometryEquiv e g).val (e x) = (a : K) • e x at h
    rw [elementaryIsometryEquiv_apply, e.symm_apply_apply] at h
    apply e.injective
    change e (g.val x) = e ((a : K) • x)
    rw [map_smul]
    exact h
  · rintro ⟨a, ha⟩
    refine ⟨a, fun x => ?_⟩
    rw [elementaryIsometryEquiv_apply, ha, map_smul, e.apply_symm_apply]

theorem scalarKernel_map_isometry (e : Q.IsometryEquiv R) :
    (scalarKernel Q).map (elementaryIsometryEquiv e).toMonoidHom = scalarKernel R := by
  ext h
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (mem_scalarKernel_isometry_iff e g).mpr hg
  · intro hh
    refine ⟨(elementaryIsometryEquiv e).symm h, ?_, (elementaryIsometryEquiv e).apply_symm_apply h⟩
    apply (mem_scalarKernel_isometry_iff e _).mp
    simpa only [MulEquiv.apply_symm_apply] using hh

theorem scalarKernel_map_isometry_symm (e : Q.IsometryEquiv R) :
    (scalarKernel R).map (elementaryIsometryEquiv e).symm.toMonoidHom = scalarKernel Q :=
  (Subgroup.map_symm_eq_iff_map_eq (scalarKernel Q)
    (e := elementaryIsometryEquiv e) (H := scalarKernel R)).mpr (scalarKernel_map_isometry e)

@[expose] def projectiveIsometryEquiv (e : Q.IsometryEquiv R) :
    ProjectiveGroup Q ≃* ProjectiveGroup R :=
  QuotientGroup.congr (scalarKernel Q) (scalarKernel R)
    (elementaryIsometryEquiv e) (scalarKernel_map_isometry e)

theorem projectiveIsometryEquiv_mk (e : Q.IsometryEquiv R) (g : elementaryGroup Q) :
    projectiveIsometryEquiv e (QuotientGroup.mk' (scalarKernel Q) g) =
      QuotientGroup.mk' (scalarKernel R) (elementaryIsometryEquiv e g) := rfl

theorem projectiveIsometryEquiv_symm_mk (e : Q.IsometryEquiv R) (g : elementaryGroup R) :
    (projectiveIsometryEquiv e).symm (QuotientGroup.mk' (scalarKernel R) g) =
      QuotientGroup.mk' (scalarKernel Q) ((elementaryIsometryEquiv e).symm g) := rfl

theorem projective_point_isometry (e : Q.IsometryEquiv R)
    (p : ProjectiveGroup Q) (L : Points Q) :
    pointIsometryEquiv e (p • L) = projectiveIsometryEquiv e p • pointIsometryEquiv e L := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (scalarKernel Q) p
  rw [projectiveIsometryEquiv_mk, quotient_smul, quotient_smul]
  exact elementary_point_isometry e g L

theorem projectivePointAction_isometry (e : Q.IsometryEquiv R) (p : ProjectiveGroup Q) :
    (pointIsometryEquiv e).permCongr (projectivePointAction Q p) =
      projectivePointAction R (projectiveIsometryEquiv e p) := by
  apply Equiv.ext
  intro L
  rw [Equiv.permCongr_apply]
  change pointIsometryEquiv e (p • (pointIsometryEquiv e).symm L) =
    projectiveIsometryEquiv e p • L
  rw [projective_point_isometry, Equiv.apply_symm_apply]

theorem projective_point_isometry_submodule (e : Q.IsometryEquiv R)
    (p : ProjectiveGroup Q) (L : Points Q) :
    (projectiveIsometryEquiv e p • pointIsometryEquiv e L).val =
      (p • L).val.map e.toLinearMap := by
  rw [← projective_point_isometry, pointIsometryEquiv_submodule]

theorem projective_point_isometry_symm (e : Q.IsometryEquiv R)
    (p : ProjectiveGroup R) (L : Points R) :
    (pointIsometryEquiv e).symm (p • L) =
      (projectiveIsometryEquiv e).symm p • (pointIsometryEquiv e).symm L := by
  apply (pointIsometryEquiv e).injective
  rw [Equiv.apply_symm_apply, projective_point_isometry,
    MulEquiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem projective_point_isometry_symm_submodule (e : Q.IsometryEquiv R)
    (p : ProjectiveGroup R) (L : Points R) :
    ((projectiveIsometryEquiv e).symm p • (pointIsometryEquiv e).symm L).val =
      (p • L).val.map e.symm.toLinearMap := by
  rw [← projective_point_isometry_symm, pointIsometryEquiv_symm_submodule]

end CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry
