module

public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
public import CFSG.Assembly.Defs

public section

namespace CFSG.ComponentClassification.PerfectPermutationActions

theorem fixed_on_small_invariant {A I : Type*} [Group A] [Group.IsPerfect A]
    (action : A →* Equiv.Perm I) (invariantSet : Set I) [Finite invariantSet]
    (hcard : Nat.card invariantSet ≤ 2)
    (hinvariant : ∀ actor : A, ∀ point : I,
      action actor point ∈ invariantSet ↔ point ∈ invariantSet) :
    ∀ actor : A, ∀ point ∈ invariantSet, action actor point = point := by
  let restriction : A →* Equiv.Perm invariantSet :=
    { toFun := fun actor => (action actor).subtypePerm (hinvariant actor)
      map_one' := by
        apply Equiv.ext
        intro point
        apply Subtype.ext
        change action 1 point.val = point.val
        rw [map_one]
        rfl
      map_mul' := by
        intro left right
        apply Equiv.ext
        intro point
        apply Subtype.ext
        change action (left * right) point.val = action left (action right point.val)
        rw [map_mul]
        rfl }
  let : IsMulCommutative (Equiv.Perm invariantSet) :=
    Equiv.Perm.isMulCommutative_iff_card_le_two.mpr hcard
  have htrivial := PerfectAutomorphisms.hom_eq_one_of_commutative restriction
  intro actor point hpoint
  exact congrArg (fun homomorphism : A →* Equiv.Perm invariantSet =>
    ((homomorphism actor) (⟨point, hpoint⟩ : invariantSet)).val) htrivial

theorem eq_one_of_small_invariant_cover {A I : Type*} [Group A] [Group.IsPerfect A]
    (action : A →* Equiv.Perm I)
    (hcover : ∀ point : I, ∃ invariantSet : Set I, invariantSet.Finite ∧
      Nat.card invariantSet ≤ 2 ∧ point ∈ invariantSet ∧
      ∀ actor : A, ∀ member : I, action actor member ∈ invariantSet ↔ member ∈ invariantSet) :
    action = 1 := by
  apply MonoidHom.ext
  intro actor
  apply Equiv.ext
  intro point
  obtain ⟨invariantSet, hfinite, hcard, hpoint, hinvariant⟩ := hcover point
  let : Finite invariantSet := hfinite.to_subtype
  exact fixed_on_small_invariant action invariantSet hcard hinvariant actor point hpoint

theorem fixed_of_involutive_pair {A I : Type*} [Group A] [Group.IsPerfect A]
    (action : A →* Equiv.Perm I) (involution : Equiv.Perm I)
    (hinvolutive : Function.Involutive involution)
    (hcommutes : ∀ actor : A, Commute involution (action actor)) (point : I)
    (hpair : ∀ actor : A, action actor point = point ∨ action actor point = involution point)
    (actor : A) : action actor point = point := by
  classical
  let invariantSet : Set I := {point, involution point}
  have hforward : ∀ acting : A, ∀ member ∈ invariantSet, action acting member ∈ invariantSet := by
    intro acting member hmember
    rcases Set.mem_insert_iff.mp hmember with hpoint | hpartner
    · subst member
      rcases hpair acting with heq | heq
      · rw [heq]
        exact Set.mem_insert _ _
      · rw [heq]
        exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
    · have heq : member = involution point := Set.mem_singleton_iff.mp hpartner
      rw [heq]
      have haction := congrArg (fun permutation : Equiv.Perm I => permutation point)
        (hcommutes acting).eq
      change involution (action acting point) = action acting (involution point) at haction
      rw [← haction]
      rcases hpair acting with heq | heq
      · rw [heq]
        exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
      · rw [heq, hinvolutive]
        exact Set.mem_insert _ _
  have hinvariant : ∀ acting : A, ∀ member : I,
      action acting member ∈ invariantSet ↔ member ∈ invariantSet := by
    intro acting member
    refine ⟨?_, hforward acting member⟩
    intro hmember
    have hinverse := hforward acting⁻¹ (action acting member) hmember
    rw [map_inv] at hinverse
    simpa only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply] using hinverse
  let : Finite invariantSet := (Set.toFinite invariantSet).to_subtype
  have hcard : Nat.card invariantSet ≤ 2 := by
    let covering : Bool → invariantSet := fun choice =>
      if choice then ⟨point, Set.mem_insert _ _⟩
        else ⟨involution point, Set.mem_insert_of_mem _ (Set.mem_singleton _)⟩
    have hsurjective : Function.Surjective covering := by
      intro member
      rcases Set.mem_insert_iff.mp member.property with hfirst | hsecond
      · exact ⟨true, Subtype.ext hfirst.symm⟩
      · exact ⟨false, Subtype.ext (Set.mem_singleton_iff.mp hsecond).symm⟩
    simpa using Nat.card_le_card_of_surjective covering hsurjective
  exact fixed_on_small_invariant action invariantSet hcard hinvariant actor point (Set.mem_insert _ _)

end CFSG.ComponentClassification.PerfectPermutationActions
