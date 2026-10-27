module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataBasic

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointData

open CatalogueBOrthogonalSemilinear CatalogueBOrthogonalPointAction

universe u

variable {K : Type u} [Field K] {d : ℕ}

instance fieldCoordinateSurjective (g : coordinateSemilinearGroup d K) :
    RingHomSurjective g.right.toRingHom := ⟨g.right.surjective⟩

@[expose] def coordinateSemilinearLinearMap (g : coordinateSemilinearGroup d K) :
    (Fin d → K) →ₛₗ[g.right.toRingHom] (Fin d → K) where
  toFun := coordinateSemilinearMap g
  map_add' := (coordinateSemilinearMap g).map_add
  map_smul' := coordinateSemilinearMap_smul g

@[expose] def similarityPointMap (Q : QuadraticForm K (Fin d → K))
    (g : similarityPairs Q) (L : Points Q) : Points Q :=
  ⟨L.val.map (coordinateSemilinearLinearMap g.val), by
    obtain ⟨x, hx, hQx, rfl⟩ := exists_eq_pointMk L
    rw [pointMk_submodule, Submodule.map_span, Set.image_singleton]
    exact finrank_span_singleton
      (fun h => hx ((coordinateSemilinearMap g.val).map_eq_zero_iff.mp h)), by
    rintro y ⟨x, hx, rfl⟩
    change Q (coordinateSemilinearMap g.val x) = 0
    rw [multiplier_spec, L.property.2 x hx, map_zero, mul_zero]⟩

theorem similarityPointMap_pointMk (Q : QuadraticForm K (Fin d → K))
    (g : similarityPairs Q) (x : Fin d → K) (hx : x ≠ 0) (hQx : Q x = 0) :
    similarityPointMap Q g (pointMk x hx hQx) =
      pointMk (coordinateSemilinearMap g.val x)
        (fun h => hx ((coordinateSemilinearMap g.val).map_eq_zero_iff.mp h))
        (by rw [multiplier_spec, hQx, map_zero, mul_zero]) := by
  apply Subtype.ext
  change (Submodule.span K {x}).map (coordinateSemilinearLinearMap g.val) = _
  rw [Submodule.map_span, Set.image_singleton, pointMk_submodule]
  rfl

theorem similarityPointMap_one (Q : QuadraticForm K (Fin d → K)) (L : Points Q) :
    similarityPointMap Q 1 L = L := by
  obtain ⟨x, hx, hQx, rfl⟩ := exists_eq_pointMk L
  rw [similarityPointMap_pointMk]
  apply Subtype.ext
  rw [pointMk_submodule, pointMk_submodule]
  change Submodule.span K {coordinateSemilinearMap (1 : coordinateSemilinearGroup d K) x} = _
  rw [coordinateSemilinearMap_one]

theorem similarityPointMap_mul (Q : QuadraticForm K (Fin d → K))
    (g h : similarityPairs Q) (L : Points Q) :
    similarityPointMap Q (g * h) L = similarityPointMap Q g (similarityPointMap Q h L) := by
  obtain ⟨x, hx, hQx, rfl⟩ := exists_eq_pointMk L
  rw [similarityPointMap_pointMk, similarityPointMap_pointMk, similarityPointMap_pointMk]
  apply Subtype.ext
  rw [pointMk_submodule, pointMk_submodule]
  change Submodule.span K {coordinateSemilinearMap (g.val * h.val) x} = _
  rw [coordinateSemilinearMap_mul]

@[expose] def similarityPointPerm (Q : QuadraticForm K (Fin d → K))
    (g : similarityPairs Q) : Equiv.Perm (Points Q) where
  toFun := similarityPointMap Q g
  invFun := similarityPointMap Q g⁻¹
  left_inv L := by
    rw [← similarityPointMap_mul, inv_mul_cancel, similarityPointMap_one]
  right_inv L := by
    rw [← similarityPointMap_mul, mul_inv_cancel, similarityPointMap_one]

@[expose] def similarityPointAction (Q : QuadraticForm K (Fin d → K)) :
    similarityPairs Q →* Equiv.Perm (Points Q) where
  toFun := similarityPointPerm Q
  map_one' := by
    apply Equiv.ext
    exact similarityPointMap_one Q
  map_mul' g h := by
    apply Equiv.ext
    exact similarityPointMap_mul Q g h

theorem similarityPointAction_submodule (Q : QuadraticForm K (Fin d → K))
    (g : similarityPairs Q) (L : Points Q) :
    (similarityPointAction Q g L).val = L.val.map (coordinateSemilinearLinearMap g.val) := rfl

end CFSG.ComponentClassification.CatalogueBOrthogonalPointData
