module

public import CFSG.CharacterTheory.TwoRankLowerBound.BinarySummandExchange

public section

open scoped Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem binary_projection_zero_left_trace {ring left right : Type*}
    [CommRing ring] [AddCommGroup left] [AddCommGroup right] [Module ring left] [Module ring right]
    [Module.Free ring left] [Module.Finite ring left] [Module.Free ring right] [Module.Finite ring right]
    (projection : Module.End ring (left × right))
    (hzeroLeft : ∀ value : left, projection (value, 0) = 0)
    (translation : Module.End ring right) :
    LinearMap.trace ring (left × right) (projection * LinearMap.prodMap LinearMap.id translation) =
      LinearMap.trace ring right (rightCoordinateProjection projection * translation) := by
  have hexpansion : projection * LinearMap.prodMap LinearMap.id translation =
      (projection.comp (LinearMap.inr ring left right)).comp
        (translation.comp (LinearMap.snd ring left right)) := by
    apply LinearMap.ext
    intro value
    change projection (value.1, translation value.2) = projection (0, translation value.2)
    rw [projection_apply_split, hzeroLeft, zero_add]
  rw [hexpansion, LinearMap.trace_comp_comm', LinearMap.trace_mul_comm]
  congr 1

theorem binary_projection_fixed_coordinate_elimination {ring left right : Type*}
    [CommRing ring] [AddCommGroup left] [AddCommGroup right] [Module ring left] [Module ring right]
    [Module.Free ring left] [Module.Finite ring left] [Module.Free ring right] [Module.Finite ring right]
    (projection : Module.End ring (left × right)) (hidempotent : IsIdempotentElem projection)
    (translation : Module.End ring right)
    (hcommute : Commute projection (LinearMap.prodMap LinearMap.id translation))
    (hunit : IsUnit (1 - (LinearMap.fst ring left right).comp
      (projection.comp (LinearMap.inl ring left right)))) :
    ∃ remainder : Module.End ring right, IsIdempotentElem remainder ∧ Commute remainder translation ∧
      LinearMap.trace ring (left × right) (projection * LinearMap.prodMap LinearMap.id translation) =
        LinearMap.trace ring right (remainder * translation) := by
  obtain ⟨unit, hunit⟩ := hunit
  let diagonal : Module.End ring (left × right) := LinearMap.prodMap LinearMap.id translation
  let inverse := (endomorphismUnitLinearEquiv unit).symm
  let sectionMap := (1 - projection).comp ((LinearMap.inl ring left right).comp inverse.toLinearMap)
  have hcoordinate : (LinearMap.fst ring left right).comp
      ((1 - projection).comp (LinearMap.inl ring left right)) =
      1 - (LinearMap.fst ring left right).comp (projection.comp (LinearMap.inl ring left right)) := by
    ext value
    simp
  have hfirst : ∀ value : left, (sectionMap value).1 = value := by
    intro value
    have hequal := congrArg (fun operator : Module.End ring left => operator (inverse value)) hunit
    rw [← hcoordinate] at hequal
    change (unit : Module.End ring left) (inverse value) = (sectionMap value).1 at hequal
    exact hequal.symm.trans ((endomorphismUnitLinearEquiv unit).apply_symm_apply value)
  have hzero : ∀ value : left, projection (sectionMap value) = 0 := by
    intro value
    have hequal : projection * (1 - projection) = 0 := by
      rw [mul_sub, mul_one, hidempotent.eq, sub_self]
    exact congrArg (fun operator : Module.End ring (left × right) => operator (inverse value, 0)) hequal
  have hsectionFixed : ∀ value : left, diagonal (sectionMap value) = sectionMap value := by
    intro value
    have hcomplement : Commute (1 - projection) diagonal := (Commute.one_left _).sub_left hcommute
    have hequal := congrArg (fun operator : Module.End ring (left × right) => operator (inverse value, 0))
      hcomplement.eq.symm
    change diagonal ((1 - projection) (inverse value, 0)) =
      (1 - projection) (diagonal (inverse value, 0)) at hequal
    have hdiag : diagonal (inverse value, 0) = (inverse value, 0) := by
      change (inverse value, translation 0) = (inverse value, 0)
      rw [map_zero]
    rw [hdiag] at hequal
    exact hequal
  let shear := splitCoordinateShear sectionMap hfirst
  let conjugate := conjugateProjection shear projection
  have hconjugate : IsIdempotentElem conjugate := conjugateProjection_isIdempotent shear projection hidempotent
  have hleft : ∀ value : left, conjugate (value, 0) = 0 := by
    intro value
    change shear.symm (projection (sectionMap value + (0, 0))) = 0
    simp only [Prod.mk_zero_zero, add_zero, hzero, map_zero]
  have hshear : shear.toLinearMap.comp diagonal = diagonal.comp shear.toLinearMap := by
    apply LinearMap.ext
    intro value
    change sectionMap value.1 + (0, translation value.2) = diagonal (sectionMap value.1 + (0, value.2))
    rw [map_add, hsectionFixed]
    rfl
  have htransport : (LinearEquiv.conjAlgEquiv ring shear.symm) diagonal = diagonal := by
    apply LinearMap.ext
    intro value
    apply shear.injective
    change shear (shear.symm (diagonal (shear value))) = shear (diagonal value)
    rw [LinearEquiv.apply_symm_apply]
    exact congrArg (fun operator : Module.End ring (left × right) => operator value) hshear.symm
  have hconjugateCommute : Commute conjugate diagonal := by
    have hequal := hcommute.map (LinearEquiv.conjAlgEquiv ring shear.symm)
    rw [htransport] at hequal
    exact hequal
  have hrightCommute : Commute (rightCoordinateProjection conjugate) translation := by
    change rightCoordinateProjection conjugate * translation = translation * rightCoordinateProjection conjugate
    apply LinearMap.ext
    intro value
    have hequal := congrArg (fun operator : Module.End ring (left × right) => (operator (0, value)).2)
      hconjugateCommute.eq
    exact hequal
  refine ⟨rightCoordinateProjection conjugate,
    rightCoordinateProjection_isIdempotent_of_left_scalar conjugate hconjugate 0 (by
      simpa only [zero_smul, Prod.mk_zero_zero] using hleft), hrightCommute, ?_⟩
  have htrace : LinearMap.trace ring (left × right) (conjugate * diagonal) =
      LinearMap.trace ring (left × right) (projection * diagonal) := by
    have hequal := LinearMap.trace_conj' (projection * diagonal) shear.symm
    change LinearMap.trace ring (left × right)
      ((LinearEquiv.conjAlgEquiv ring shear.symm) (projection * diagonal)) = _ at hequal
    rw [map_mul, htransport] at hequal
    exact hequal
  rw [← htrace]
  exact binary_projection_zero_left_trace conjugate hleft translation

end CFSG.TwoRankLowerBound.Helpers
