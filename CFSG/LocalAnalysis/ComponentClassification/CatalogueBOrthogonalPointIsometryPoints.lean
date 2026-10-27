module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointIsometryBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionBasic

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CatalogueBOrthogonalPointAction

universe u v w

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {W : Type w} [AddCommGroup W] [Module K W]
variable {Q : QuadraticForm K V} {R : QuadraticForm K W}

@[expose] def pointIsometryMap (e : Q.IsometryEquiv R) (L : Points Q) : Points R :=
  ⟨L.val.map e.toLinearMap, (e.toLinearEquiv.finrank_map_eq L.val).trans L.property.1, by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact (e.map_app x).trans (L.property.2 x hx)⟩

theorem submodule_isometry_inverse (e : Q.IsometryEquiv R) (L : Submodule K V) :
    (L.map e.toLinearMap).map e.symm.toLinearMap = L := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, hyx⟩
    change e.symm (e z) = x at hyx
    rw [e.symm_apply_apply] at hyx
    exact hyx ▸ hz
  · intro hx
    exact ⟨e x, ⟨x, hx, rfl⟩, e.symm_apply_apply x⟩

@[expose] def pointIsometryEquiv (e : Q.IsometryEquiv R) : Points Q ≃ Points R where
  toFun := pointIsometryMap e
  invFun := pointIsometryMap e.symm
  left_inv L := Subtype.ext (submodule_isometry_inverse e L.val)
  right_inv L := Subtype.ext (submodule_isometry_inverse e.symm L.val)

theorem pointIsometryEquiv_submodule (e : Q.IsometryEquiv R) (L : Points Q) :
    (pointIsometryEquiv e L).val = L.val.map e.toLinearMap := rfl

theorem pointIsometryEquiv_symm_submodule (e : Q.IsometryEquiv R) (L : Points R) :
    ((pointIsometryEquiv e).symm L).val = L.val.map e.symm.toLinearMap := rfl

theorem mem_pointIsometryEquiv (e : Q.IsometryEquiv R) (L : Points Q) (y : W) :
    y ∈ (pointIsometryEquiv e L).val ↔ e.symm y ∈ L.val := by
  change y ∈ L.val.map e.toLinearMap ↔ _
  exact Submodule.mem_map_equiv L.val (e := e.toLinearEquiv) (x := y)

theorem mem_pointIsometryEquiv_symm (e : Q.IsometryEquiv R) (L : Points R) (x : V) :
    x ∈ ((pointIsometryEquiv e).symm L).val ↔ e x ∈ L.val := by
  change x ∈ L.val.map e.symm.toLinearMap ↔ _
  exact Submodule.mem_map_equiv L.val (e := e.symm.toLinearEquiv) (x := x)

theorem pointPerp_isometry_iff (e : Q.IsometryEquiv R) (L M : Points Q) :
    PointPerp (pointIsometryEquiv e L) (pointIsometryEquiv e M) ↔ PointPerp L M := by
  constructor
  · intro h x hx y hy
    have hx' : e x ∈ (pointIsometryEquiv e L).val := ⟨x, hx, rfl⟩
    have hy' : e y ∈ (pointIsometryEquiv e M).val := ⟨y, hy, rfl⟩
    exact (polar_isometry e x y).symm.trans (h (e x) hx' (e y) hy')
  · intro h x hx y hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact (polar_isometry e a b).trans (h a ha b hb)

theorem pointPerp_isometry_symm_iff (e : Q.IsometryEquiv R) (L M : Points R) :
    PointPerp ((pointIsometryEquiv e).symm L) ((pointIsometryEquiv e).symm M) ↔
      PointPerp L M :=
  pointPerp_isometry_iff e.symm L M

theorem elementary_point_isometry (e : Q.IsometryEquiv R)
    (g : elementaryGroup Q) (L : Points Q) :
    pointIsometryEquiv e (g • L) = elementaryIsometryEquiv e g • pointIsometryEquiv e L := by
  apply Subtype.ext
  rw [pointIsometryEquiv_submodule, elementary_smul_submodule,
    elementary_smul_submodule, pointIsometryEquiv_submodule]
  ext y
  constructor
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨e x, ⟨x, hx, rfl⟩, ?_⟩
    change (elementaryIsometryEquiv e g).val (e x) = e (g.val x)
    rw [elementaryIsometryEquiv_apply, e.symm_apply_apply]
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨g.val x, ⟨x, hx, rfl⟩, ?_⟩
    change e (g.val x) = (elementaryIsometryEquiv e g).val (e x)
    rw [elementaryIsometryEquiv_apply, e.symm_apply_apply]

theorem elementaryPointAction_isometry (e : Q.IsometryEquiv R) (g : elementaryGroup Q) :
    (pointIsometryEquiv e).permCongr (elementaryPointAction Q g) =
      elementaryPointAction R (elementaryIsometryEquiv e g) := by
  apply Equiv.ext
  intro L
  rw [Equiv.permCongr_apply]
  change pointIsometryEquiv e (g • (pointIsometryEquiv e).symm L) =
    elementaryIsometryEquiv e g • L
  rw [elementary_point_isometry, Equiv.apply_symm_apply]

end CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry
