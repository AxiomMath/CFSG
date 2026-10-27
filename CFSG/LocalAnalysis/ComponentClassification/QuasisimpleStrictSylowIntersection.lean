module

public import CFSG.LocalAnalysis.ComponentClassification.QuasisimpleInvolutionProduct

public section

open CFSG.Open

namespace CFSG.ComponentClassification.QuasisimpleStrictSylowIntersection

theorem not_contained {G : Type*} [Group G] [Finite G]
    (ambient intersection central acting : Subgroup G)
    (hquasisimple : IsQuasisimple ambient) (heven : Even (Nat.card ambient))
    (hcentral : central ≤ (Subgroup.center ambient).map ambient.subtype)
    (hinvolutions : ∀ member ∈ intersection, orderOf member = 2 → member ∈ central)
    (helementary : IsElemAbelian 2 acting) (hnontrivial : Nontrivial acting)
    (hnormalizes : acting ≤ Subgroup.normalizer (ambient : Set G))
    (hdisjoint : Disjoint ambient acting)
    (hcentralizes : acting ≤ Subgroup.centralizer (intersection : Set G))
    (hfaithful : Function.Injective (ambient.normalizerMonoidHom.comp (Subgroup.inclusion hnormalizes)))
    (sylow : Sylow 2 ambient) :
    ¬ (sylow : Subgroup ambient).map ambient.subtype ≤ intersection := by
  intro hcontained
  obtain ⟨member, hmember, hne⟩ := acting.nontrivial_iff_exists_ne_one.mp hnontrivial
  have horder : orderOf member = 2 := orderOf_eq_prime (helementary.2 member hmember) hne
  have hcyclic : Subgroup.zpowers member ≤ acting := Subgroup.zpowers_le.mpr hmember
  have hsquares : ∀ element ∈ (sylow : Subgroup ambient).map ambient.subtype,
      element ^ 2 = 1 → element ∈ (Subgroup.center ambient).map ambient.subtype := by
    intro element helement hsquare
    by_cases hone : element = 1
    · rw [hone]
      exact ((Subgroup.center ambient).map ambient.subtype).one_mem
    · exact hcentral (hinvolutions element (hcontained helement) (orderOf_eq_prime hsquare hone))
  have hcentralFixed : member ∈ Subgroup.centralizer
      (((sylow : Subgroup ambient).map ambient.subtype : Subgroup G) : Set G) :=
    Subgroup.centralizer_le hcontained (hcentralizes hmember)
  have hcentralAmbient := QuasisimpleInvolutionProduct.centralizes ambient hquasisimple heven member horder
    (hnormalizes hmember) (hdisjoint.mono le_rfl hcyclic) sylow hcentralFixed hsquares
  have hkernel : Subgroup.inclusion hnormalizes (⟨member, hmember⟩ : acting) ∈ ambient.normalizerMonoidHom.ker := by
    rw [Subgroup.normalizerMonoidHom_ker]
    exact hcentralAmbient
  have hactionOne : (ambient.normalizerMonoidHom.comp (Subgroup.inclusion hnormalizes))
      (⟨member, hmember⟩ : acting) = 1 := MonoidHom.mem_ker.mp hkernel
  have hmemberOne : (⟨member, hmember⟩ : acting) = 1 := hfaithful (hactionOne.trans (map_one _).symm)
  exact hne (congrArg Subtype.val hmemberOne)

theorem card_lt {G : Type*} [Group G] [Finite G]
    (ambient intersection : Subgroup G) (hintersection : intersection ≤ ambient)
    (hnotContained : ∀ sylow : Sylow 2 ambient, ¬ (sylow : Subgroup ambient).map ambient.subtype ≤ intersection)
    (first : Sylow 2 intersection) (second : Sylow 2 ambient) :
    Nat.card (first : Subgroup intersection) < Nat.card (second : Subgroup ambient) := by
  let firstImage := (first : Subgroup intersection).map intersection.subtype
  have hfirstIntersection : firstImage ≤ intersection := by
    rintro member ⟨lift, hlift, rfl⟩
    exact lift.property
  have hfirstAmbient := hfirstIntersection.trans hintersection
  have htwo : IsPGroup 2 firstImage := first.isPGroup'.map intersection.subtype
  obtain ⟨containing, hcontained⟩ := (htwo.comap_subtype (K := ambient)).exists_le_sylow
  have hle : firstImage ≤ (containing : Subgroup ambient).map ambient.subtype := by
    have hmap := Subgroup.map_mono (f := ambient.subtype) hcontained
    change (firstImage.subgroupOf ambient).map ambient.subtype ≤ (containing : Subgroup ambient).map ambient.subtype at hmap
    rw [Subgroup.map_subgroupOf_eq_of_le hfirstAmbient] at hmap
    exact hmap
  have hcardLe := Nat.card_le_card_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  have hlt : Nat.card firstImage < Nat.card ((containing : Subgroup ambient).map ambient.subtype) := by
    apply lt_of_le_of_ne hcardLe
    intro hequal
    have hsame := Subgroup.eq_of_le_of_card_ge hle hequal.ge
    apply hnotContained containing
    rw [← hsame]
    exact hfirstIntersection
  rw [Subgroup.card_map_of_injective intersection.subtype_injective,
    Subgroup.card_map_of_injective ambient.subtype_injective] at hlt
  rwa [containing.card_eq_multiplicity, ← second.card_eq_multiplicity] at hlt

end CFSG.ComponentClassification.QuasisimpleStrictSylowIntersection
