module

public import CFSG.Assembly.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.ComponentClassification.SubgroupSylowTransport

theorem exists_image {G : Type*} [Group G] [Finite G]
    (first second : Subgroup G) (automorphism : G ≃* G)
    (heq : first.map automorphism.toMonoidHom = second) (sylow : Sylow 2 first) :
    ∃ transported : Sylow 2 second,
      (transported : Subgroup second).map second.subtype =
        ((sylow : Subgroup first).map first.subtype).map automorphism.toMonoidHom := by
  let equivalence := (first.equivMapOfInjective automorphism.toMonoidHom automorphism.injective).trans
    (MulEquiv.subgroupCongr heq)
  have hsurjective : Function.Surjective equivalence.toMonoidHom := equivalence.surjective
  let transported := sylow.mapSurjective (f := equivalence.toMonoidHom) hsurjective
  refine ⟨transported, ?_⟩
  change (sylow.mapSurjective (f := equivalence.toMonoidHom) hsurjective : Subgroup second).map second.subtype = _
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  have hhomomorphism : second.subtype.comp equivalence.toMonoidHom = automorphism.toMonoidHom.comp first.subtype := by
    ext member
    change ((MulEquiv.subgroupCongr heq) ((first.equivMapOfInjective automorphism.toMonoidHom automorphism.injective) member)).val = _
    rw [MulEquiv.subgroupCongr_apply]
    rfl
  rw [hhomomorphism]

theorem same_card {G : Type*} [Group G] [Finite G] (first second : Sylow 2 G) :
    Nat.card (first : Subgroup G) = Nat.card (second : Subgroup G) := by
  rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]

theorem card_eq {G : Type*} [Group G] [Finite G]
    (first second : Subgroup G) (automorphism : G ≃* G)
    (heq : first.map automorphism.toMonoidHom = second)
    (firstSylow : Sylow 2 first) (secondSylow : Sylow 2 second) :
    Nat.card (firstSylow : Subgroup first) = Nat.card (secondSylow : Subgroup second) := by
  obtain ⟨transported, htransported⟩ := exists_image first second automorphism heq firstSylow
  have hcard := congrArg (fun subgroup : Subgroup G => Nat.card subgroup) htransported
  rw [Subgroup.card_map_of_injective second.subtype_injective,
    Subgroup.card_map_of_injective automorphism.injective,
    Subgroup.card_map_of_injective first.subtype_injective] at hcard
  exact hcard.symm.trans (same_card transported secondSylow)

theorem centralizer_conjugate {G : Type*} [Group G]
    (subgroup : Subgroup G) (actor : G) (hcentral : actor ∈ Subgroup.centralizer (subgroup : Set G)) :
    subgroup.map (MulAut.conj actor).toMonoidHom = subgroup := by
  ext member
  constructor
  · rintro ⟨lift, hlift, rfl⟩
    have hcommute := Subgroup.mem_centralizer_iff.mp hcentral lift hlift
    change actor * lift * actor⁻¹ ∈ subgroup
    rw [← hcommute, mul_inv_cancel_right]
    exact hlift
  · intro hmember
    refine Subgroup.mem_map.mpr ⟨member, hmember, ?_⟩
    have hcommute := Subgroup.mem_centralizer_iff.mp hcentral member hmember
    change actor * member * actor⁻¹ = member
    rw [← hcommute, mul_inv_cancel_right]

theorem unique_eq_of_centralizer {G : Type*} [Group G] [Finite G]
    (first second : Subgroup G) (actor : G)
    (heq : first.map (MulAut.conj actor).toMonoidHom = second)
    (firstSylow : Sylow 2 first) (secondSylow : Sylow 2 second)
    (hunique : ∀ other : Sylow 2 second, other = secondSylow)
    (hcentral : actor ∈ Subgroup.centralizer ((firstSylow : Subgroup first).map first.subtype : Set G)) :
    (firstSylow : Subgroup first).map first.subtype = (secondSylow : Subgroup second).map second.subtype := by
  obtain ⟨transported, htransported⟩ := exists_image first second (MulAut.conj actor) heq firstSylow
  rw [hunique transported, centralizer_conjugate _ actor hcentral] at htransported
  exact htransported.symm

end CFSG.ComponentClassification.SubgroupSylowTransport
