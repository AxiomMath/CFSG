module

public import CFSG.Open.LocalVocabulary

public section

open CFSG.Open
open CFSG.Open
open scoped commutatorElement

namespace CFSG.RankThreeCoreUniqueness.Helpers

theorem central_subgroup_normal
    {G : Type*} [Group G] (centralGroup : Subgroup G)
    (hcentral : centralGroup ≤ Subgroup.center G) : centralGroup.Normal := by
  refine ⟨?_⟩
  intro element helement conjugator
  have hcommute := Subgroup.mem_center_iff.mp (hcentral helement) conjugator
  rw [hcommute, mul_assoc, mul_inv_cancel, mul_one]
  exact helement

theorem commutator_central_join_eq
    {G : Type*} [Group G] (subgroup centralGroup : Subgroup G)
    (hcentral : centralGroup ≤ Subgroup.center G) :
    ⁅subgroup ⊔ centralGroup, subgroup ⊔ centralGroup⁆ = ⁅subgroup, subgroup⁆ := by
  let : centralGroup.Normal := central_subgroup_normal centralGroup hcentral
  apply le_antisymm _ (Subgroup.commutator_mono le_sup_left le_sup_left)
  apply Subgroup.commutator_le.mpr
  intro first hfirst second hsecond
  obtain ⟨firstSubgroup, hfirstSubgroup, firstCentral, hfirstCentral, rfl⟩ :=
    Subgroup.mem_sup_of_normal_right.mp hfirst
  obtain ⟨secondSubgroup, hsecondSubgroup, secondCentral, hsecondCentral, rfl⟩ :=
    Subgroup.mem_sup_of_normal_right.mp hsecond
  have hfirstZero : ⁅firstCentral, secondSubgroup * secondCentral⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_center_iff.mp (hcentral hfirstCentral) _).symm
  have hsecondZero : ⁅firstSubgroup, secondCentral⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_center_iff.mp (hcentral hsecondCentral) _)
  rw [commutatorElement_mul_left_eq_conj_mul, hfirstZero,
    mul_one, mul_inv_cancel, one_mul,
    commutatorElement_mul_right_eq_mul_conj, hsecondZero]
  simpa only [mul_one, mul_inv_cancel_right] using
    Subgroup.commutator_mem_commutator hfirstSubgroup hsecondSubgroup

theorem perfect_subgroup_eq_derived_of_image_preimage
    {G Image : Type*} [Group G] [Group Image]
    (homomorphism : G →* Image) (hcentral : homomorphism.ker ≤ Subgroup.center G)
    (perfectGroup : Subgroup G) (hperfect : Group.IsPerfect perfectGroup) :
    ⁅Subgroup.comap homomorphism (Subgroup.map homomorphism perfectGroup),
      Subgroup.comap homomorphism (Subgroup.map homomorphism perfectGroup)⁆ = perfectGroup := by
  let : Group.IsPerfect perfectGroup := hperfect
  rw [Subgroup.comap_map_eq, commutator_central_join_eq perfectGroup homomorphism.ker hcentral,
    Subgroup.commutator_eq_self]

theorem perfect_lifts_with_same_image_eq
    {G Image : Type*} [Group G] [Group Image]
    (homomorphism : G →* Image) (hcentral : homomorphism.ker ≤ Subgroup.center G)
    (first second : Subgroup G) (hfirst : Group.IsPerfect first)
    (hsecond : Group.IsPerfect second)
    (himages : Subgroup.map homomorphism first = Subgroup.map homomorphism second) :
    first = second := by
  rw [← perfect_subgroup_eq_derived_of_image_preimage homomorphism hcentral first hfirst,
    himages, perfect_subgroup_eq_derived_of_image_preimage homomorphism hcentral second hsecond]

theorem perfect_lift_normalizer_contains_image_normalizer
    {G Image : Type*} [Group G] [Group Image]
    (homomorphism : G →* Image) (hcentral : homomorphism.ker ≤ Subgroup.center G)
    (perfectGroup : Subgroup G) (hperfect : Group.IsPerfect perfectGroup) :
    Subgroup.comap homomorphism
      (Subgroup.normalizer (Subgroup.map homomorphism perfectGroup : Set Image)) ≤
        Subgroup.normalizer (perfectGroup : Set G) := by
  intro conjugator hconjugator
  have hpreimageNormalizes : conjugator ∈ Subgroup.normalizer
      (Subgroup.comap homomorphism (Subgroup.map homomorphism perfectGroup) : Set G) := by
    apply Subgroup.mem_normalizer_iff.mpr
    intro element
    change homomorphism element ∈ Subgroup.map homomorphism perfectGroup ↔
      homomorphism (conjugator * element * conjugator⁻¹) ∈ Subgroup.map homomorphism perfectGroup
    simpa only [map_mul, map_inv] using
      Subgroup.mem_normalizer_iff.mp hconjugator (homomorphism element)
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  have hmap := Subgroup.mem_normalizer_iff_map_conj_eq.mp hpreimageNormalizes
  rw [← perfect_subgroup_eq_derived_of_image_preimage homomorphism hcentral perfectGroup hperfect,
    Subgroup.map_commutator, hmap]

end CFSG.RankThreeCoreUniqueness.Helpers
