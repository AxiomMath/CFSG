module

public import CFSG.CharacterTheory.TwoRankLowerBound.SplitSummandShear

public section

open scoped Classical

namespace CFSG.TwoRankLowerBound.Helpers

@[expose] noncomputable def rightCoordinateProjection {ring left right : Type*} [Ring ring]
    [AddCommGroup left] [AddCommGroup right] [Module ring left] [Module ring right]
    (projection : Module.End ring (left × right)) : Module.End ring right :=
  (LinearMap.snd ring left right).comp (projection.comp (LinearMap.inr ring left right))

theorem projection_apply_split {ring left right : Type*} [Ring ring]
    [AddCommGroup left] [AddCommGroup right] [Module ring left] [Module ring right]
    (projection : Module.End ring (left × right)) (first : left) (second : right) :
    projection (first, second) = projection (first, 0) + projection (0, second) := by
  rw [← map_add]
  congr 1
  simp

theorem rightCoordinateProjection_isIdempotent_of_left_scalar {ring left right : Type*}
    [Ring ring] [AddCommGroup left] [AddCommGroup right] [Module ring left] [Module ring right]
    (projection : Module.End ring (left × right)) (hidempotent : IsIdempotentElem projection)
    (scalar : ring) (hleft : ∀ element : left, projection (element, 0) = (scalar • element, 0)) :
    IsIdempotentElem (rightCoordinateProjection projection) := by
  apply isIdempotentElem_iff.mpr
  ext element
  have hvalue := congrArg (fun operator : Module.End ring (left × right) => operator (0, element))
    hidempotent.eq
  have hsecond := congrArg Prod.snd hvalue
  change (projection (projection (0, element))).2 = (projection (0, element)).2 at hsecond
  rw [projection_apply_split, hleft] at hsecond
  change (projection (0, (projection (0, element)).2)).2 = (projection (0, element)).2
  simpa only [Prod.snd_add, zero_add] using hsecond

theorem projection_fixed_left_right_fixed {ring left right : Type*} [Ring ring]
    [AddCommGroup left] [AddCommGroup right] [Module ring left] [Module ring right]
    (projection : Module.End ring (left × right)) (hidempotent : IsIdempotentElem projection)
    (hleft : ∀ element : left, projection (element, 0) = (element, 0))
    (element : right) (hfixed : rightCoordinateProjection projection element = element) :
    projection (0, element) = (0, element) := by
  have hvalue := congrArg (fun operator : Module.End ring (left × right) => operator (0, element))
    hidempotent.eq
  change projection (projection (0, element)) = projection (0, element) at hvalue
  have hsecond : (projection (0, element)).2 = element := hfixed
  have hfirst := congrArg Prod.fst hvalue
  rw [projection_apply_split, hleft, hsecond] at hfirst
  have hzero : (projection (0, element)).1 = 0 := by
    simpa only [Prod.fst_add, add_eq_left] using hfirst
  exact Prod.ext hzero hsecond

theorem projection_fixed_left_range_product {ring left right : Type*} [Ring ring]
    [AddCommGroup left] [AddCommGroup right] [Module ring left] [Module ring right]
    (projection : Module.End ring (left × right)) (hidempotent : IsIdempotentElem projection)
    (hleft : ∀ element : left, projection (element, 0) = (element, 0)) :
    Nonempty (projection.range ≃ₗ[ring] (left × (rightCoordinateProjection projection).range)) := by
  have hright := rightCoordinateProjection_isIdempotent_of_left_scalar projection hidempotent 1
    (by simpa only [one_smul] using hleft)
  let forward : projection.range →ₗ[ring] left × (rightCoordinateProjection projection).range :=
    ((LinearMap.fst ring left right).comp projection.range.subtype).prod
      ((LinearMap.snd ring left right).comp projection.range.subtype |>.codRestrict _ (by
        intro element
        apply (LinearMap.IsIdempotentElem.mem_range_iff hright).mpr
        have hfixed := (LinearMap.IsIdempotentElem.mem_range_iff hidempotent).mp element.property
        have hsecond := congrArg Prod.snd hfixed
        rw [projection_apply_split, hleft] at hsecond
        change (projection (0, (element : left × right).2)).2 = (element : left × right).2
        simpa only [Prod.snd_add, zero_add] using hsecond))
  let backward : (left × (rightCoordinateProjection projection).range) →ₗ[ring] projection.range :=
    (LinearMap.prodMap (LinearMap.id : left →ₗ[ring] left)
      (rightCoordinateProjection projection).range.subtype).codRestrict _ (by
        intro element
        apply (LinearMap.IsIdempotentElem.mem_range_iff hidempotent).mpr
        change projection (element.1, (element.2 : right)) = (element.1, (element.2 : right))
        rw [projection_apply_split, hleft,
          projection_fixed_left_right_fixed projection hidempotent hleft element.2
            ((LinearMap.IsIdempotentElem.mem_range_iff hright).mp element.2.property)]
        simp)
  refine ⟨LinearEquiv.ofLinearMap forward backward ?_ ?_⟩
  · apply LinearMap.ext
    intro element
    exact Prod.ext rfl (Subtype.ext rfl)
  · apply LinearMap.ext
    intro element
    exact Subtype.ext rfl

theorem projection_zero_left_range_right {ring left right : Type*} [Ring ring]
    [AddCommGroup left] [AddCommGroup right] [Module ring left] [Module ring right]
    (projection : Module.End ring (left × right)) (hidempotent : IsIdempotentElem projection)
    (hleft : ∀ element : left, projection (element, 0) = 0) :
    Nonempty (projection.range ≃ₗ[ring] (rightCoordinateProjection projection).range) := by
  have hright := rightCoordinateProjection_isIdempotent_of_left_scalar projection hidempotent 0
    (by simpa only [zero_smul, Prod.mk_zero_zero] using hleft)
  let forward : projection.range →ₗ[ring] (rightCoordinateProjection projection).range :=
    ((LinearMap.snd ring left right).comp projection.range.subtype).codRestrict _ (by
      intro element
      apply (LinearMap.IsIdempotentElem.mem_range_iff hright).mpr
      have hfixed := (LinearMap.IsIdempotentElem.mem_range_iff hidempotent).mp element.property
      have hsecond := congrArg Prod.snd hfixed
      rw [projection_apply_split, hleft, zero_add] at hsecond
      exact hsecond)
  let backward : (rightCoordinateProjection projection).range →ₗ[ring] projection.range :=
    (projection.comp ((LinearMap.inr ring left right).comp
      (rightCoordinateProjection projection).range.subtype)).codRestrict _
        (fun element => LinearMap.mem_range_self projection _)
  refine ⟨LinearEquiv.ofLinearMap forward backward ?_ ?_⟩
  · apply LinearMap.ext
    intro element
    apply Subtype.ext
    exact (LinearMap.IsIdempotentElem.mem_range_iff hright).mp element.property
  · apply LinearMap.ext
    intro element
    apply Subtype.ext
    have hfixed := (LinearMap.IsIdempotentElem.mem_range_iff hidempotent).mp element.property
    rw [projection_apply_split, hleft, zero_add] at hfixed
    exact congrArg (fun value : left × right => value) hfixed

theorem conjugateProjection_range_equiv {ring vector : Type*} [Ring ring]
    [AddCommGroup vector] [Module ring vector] (equivalence : vector ≃ₗ[ring] vector)
    (projection : Module.End ring vector) :
    Nonempty ((conjugateProjection equivalence projection).range ≃ₗ[ring] projection.range) := by
  let forward := equivalence.toLinearMap.domRestrict (conjugateProjection equivalence projection).range
  let backward := equivalence.symm.toLinearMap.domRestrict projection.range
  let forwardRestricted := forward.codRestrict projection.range (by
    intro element
    obtain ⟨preimage, hpreimage⟩ := element.property
    refine ⟨equivalence preimage, ?_⟩
    change projection (equivalence preimage) = equivalence (element : vector)
    rw [← hpreimage]
    simp only [conjugateProjection, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply])
  let backwardRestricted := backward.codRestrict (conjugateProjection equivalence projection).range (by
    intro element
    obtain ⟨preimage, hpreimage⟩ := element.property
    refine ⟨equivalence.symm preimage, ?_⟩
    change conjugateProjection equivalence projection (equivalence.symm preimage) =
      equivalence.symm (element : vector)
    rw [← hpreimage]
    simp only [conjugateProjection, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply])
  refine ⟨LinearEquiv.ofLinearMap forwardRestricted backwardRestricted ?_ ?_⟩
  · apply LinearMap.ext
    intro element
    exact Subtype.ext (equivalence.apply_symm_apply element)
  · apply LinearMap.ext
    intro element
    exact Subtype.ext (equivalence.symm_apply_apply element)

theorem binary_local_endomorphism_summand_exchange {ring left right : Type*} [Ring ring]
    [AddCommGroup left] [AddCommGroup right] [Module ring left] [Module ring right]
    (hlocal : ∀ operator : Module.End ring left, IsUnit operator ∨ IsUnit (1 - operator))
    (projection : Module.End ring (left × right)) (hidempotent : IsIdempotentElem projection) :
    ∃ remainder : Module.End ring right, IsIdempotentElem remainder ∧
      (Nonempty (projection.range ≃ₗ[ring] (left × remainder.range)) ∨
        Nonempty (projection.range ≃ₗ[ring] remainder.range)) := by
  let coordinate := (LinearMap.fst ring left right).comp
    (projection.comp (LinearMap.inl ring left right))
  rcases hlocal coordinate with hunit | hcomplementUnit
  · obtain ⟨sectionMap, hfirst, hfixed⟩ := idempotent_coordinate_section projection hidempotent hunit
    let shear := splitCoordinateShear sectionMap hfirst
    let conjugate := conjugateProjection shear projection
    have hconjugate : IsIdempotentElem conjugate := conjugateProjection_isIdempotent _ _ hidempotent
    have hleft : ∀ element : left, conjugate (element, 0) = (element, 0) :=
      shear_conjugateProjection_fixes_left projection sectionMap hfirst hfixed
    obtain ⟨rangeEquiv⟩ := conjugateProjection_range_equiv shear projection
    obtain ⟨productEquiv⟩ := projection_fixed_left_range_product conjugate hconjugate hleft
    exact ⟨rightCoordinateProjection conjugate,
      rightCoordinateProjection_isIdempotent_of_left_scalar conjugate hconjugate 1
        (by simpa only [one_smul] using hleft), Or.inl ⟨rangeEquiv.symm.trans productEquiv⟩⟩
  · have hcomplementCoordinate : (LinearMap.fst ring left right).comp
        ((1 - projection).comp (LinearMap.inl ring left right)) = 1 - coordinate := by
      ext element
      simp [coordinate]
    have hcomplementUnit' : IsUnit ((LinearMap.fst ring left right).comp
        ((1 - projection).comp (LinearMap.inl ring left right))) :=
      hcomplementCoordinate ▸ hcomplementUnit
    obtain ⟨sectionMap, hfirst, hfixed⟩ :=
      idempotent_coordinate_section (1 - projection) hidempotent.one_sub hcomplementUnit'
    let shear := splitCoordinateShear sectionMap hfirst
    let conjugate := conjugateProjection shear projection
    have hconjugate : IsIdempotentElem conjugate := conjugateProjection_isIdempotent _ _ hidempotent
    have hzero : ∀ element, projection (sectionMap element) = 0 := by
      intro element
      have hvalue := hfixed element
      change sectionMap element - projection (sectionMap element) = sectionMap element at hvalue
      exact sub_eq_self.mp hvalue
    have hleft : ∀ element : left, conjugate (element, 0) = 0 := by
      intro element
      change shear.symm (projection (sectionMap element + (0, 0))) = 0
      simp only [Prod.mk_zero_zero, add_zero, hzero, map_zero]
    obtain ⟨rangeEquiv⟩ := conjugateProjection_range_equiv shear projection
    obtain ⟨remainderEquiv⟩ := projection_zero_left_range_right conjugate hconjugate hleft
    exact ⟨rightCoordinateProjection conjugate,
      rightCoordinateProjection_isIdempotent_of_left_scalar conjugate hconjugate 0
        (by simpa only [zero_smul, Prod.mk_zero_zero] using hleft),
      Or.inr ⟨rangeEquiv.symm.trans remainderEquiv⟩⟩

end CFSG.TwoRankLowerBound.Helpers
