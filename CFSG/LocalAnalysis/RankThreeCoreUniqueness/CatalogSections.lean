module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.SectionTransport

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def HasCatalogSimpleSections (G : Type*) [Group G] : Prop :=
  ∀ sectionGroup : Subgroup G, ∀ kernelGroup : Subgroup sectionGroup,
    ∀ hnormal : kernelGroup.Normal, letI := hnormal;
      IsSimpleGroup (sectionGroup ⧸ kernelGroup) →
      (∃ first second : sectionGroup ⧸ kernelGroup, first * second ≠ second * first) →
      Nat.card (sectionGroup ⧸ kernelGroup) ∈ knownSimpleOrders

theorem kProper_proper_subgroup_hasCatalogSimpleSections
    {G : Type*} [Group G] (hK : IsKProperByOrder G)
    (overgroup : Subgroup G) (hproper : overgroup ≠ ⊤) : HasCatalogSimpleSections overgroup := by
  intro sectionGroup kernelGroup hnormal hsimple hnonab
  let : kernelGroup.Normal := hnormal
  let : IsSimpleGroup (sectionGroup ⧸ kernelGroup) := hsimple
  exact kProper_proper_subgroup_image_simple_subgroup_image_order hK overgroup hproper
    (MonoidHom.id overgroup) Function.surjective_id sectionGroup
    (QuotientGroup.mk' kernelGroup) (QuotientGroup.mk'_surjective _) hnonab

theorem catalog_simple_subgroup_surjective_image_order
    {G : Type*} [Group G] (hcatalog : HasCatalogSimpleSections G)
    (sectionGroup : Subgroup G) {Target : Type*} [Group Target] [IsSimpleGroup Target]
    (homomorphism : sectionGroup →* Target) (hsurjective : Function.Surjective homomorphism)
    (hnonab : ∃ first second : Target, first * second ≠ second * first) :
    Nat.card Target ∈ knownSimpleOrders := by
  let quotientEquiv := QuotientGroup.quotientKerEquivOfSurjective homomorphism hsurjective
  have hsimple : IsSimpleGroup (sectionGroup ⧸ homomorphism.ker) := quotientEquiv.isSimpleGroup
  have hquotientNonab : ∃ first second : sectionGroup ⧸ homomorphism.ker,
      first * second ≠ second * first := by
    obtain ⟨first, second, hdistinct⟩ := hnonab
    refine ⟨quotientEquiv.symm first, quotientEquiv.symm second, ?_⟩
    intro hequal
    apply hdistinct
    simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg quotientEquiv hequal
  have horder := hcatalog sectionGroup homomorphism.ker inferInstance hsimple hquotientNonab
  rwa [Nat.card_congr quotientEquiv.toEquiv] at horder

theorem catalog_simple_surjective_image_order
    {G : Type*} [Group G] (hcatalog : HasCatalogSimpleSections G)
    {Target : Type*} [Group Target] [IsSimpleGroup Target]
    (homomorphism : G →* Target) (hsurjective : Function.Surjective homomorphism)
    (hnonab : ∃ first second : Target, first * second ≠ second * first) :
    Nat.card Target ∈ knownSimpleOrders :=
  catalog_simple_subgroup_surjective_image_order hcatalog (⊤ : Subgroup G)
    (homomorphism.comp (Subgroup.topEquiv (G := G)).toMonoidHom)
    (hsurjective.comp (Subgroup.topEquiv (G := G)).surjective) hnonab

theorem catalog_simple_subgroup_image_order
    {G Image : Type*} [Group G] [Group Image] (hcatalog : HasCatalogSimpleSections G)
    (homomorphism : G →* Image) (hsurjective : Function.Surjective homomorphism)
    (sectionGroup : Subgroup Image) {Target : Type*} [Group Target] [IsSimpleGroup Target]
    (sectionMap : sectionGroup →* Target) (hsectionSurjective : Function.Surjective sectionMap)
    (hnonab : ∃ first second : Target, first * second ≠ second * first) :
    Nat.card Target ∈ knownSimpleOrders := by
  let preimageGroup := Subgroup.comap homomorphism sectionGroup
  let restrictedMap : preimageGroup →* sectionGroup :=
    (homomorphism.comp preimageGroup.subtype).codRestrict sectionGroup
      (fun element => element.property)
  have hrestrictedSurjective : Function.Surjective restrictedMap := by
    intro element
    obtain ⟨preimage, hpreimage⟩ := hsurjective element.val
    have hmem : preimage ∈ preimageGroup := by
      change homomorphism preimage ∈ sectionGroup
      rw [hpreimage]
      exact element.property
    exact ⟨⟨preimage, hmem⟩, Subtype.ext hpreimage⟩
  exact catalog_simple_subgroup_surjective_image_order hcatalog preimageGroup
    (sectionMap.comp restrictedMap) (hsectionSurjective.comp hrestrictedSurjective) hnonab

theorem catalogSections_surjective
    {G Image : Type*} [Group G] [Group Image] (hcatalog : HasCatalogSimpleSections G)
    (homomorphism : G →* Image) (hsurjective : Function.Surjective homomorphism) :
    HasCatalogSimpleSections Image := by
  intro sectionGroup kernelGroup hnormal hsimple hnonab
  let : kernelGroup.Normal := hnormal
  let : IsSimpleGroup (sectionGroup ⧸ kernelGroup) := hsimple
  exact catalog_simple_subgroup_image_order hcatalog homomorphism hsurjective sectionGroup
    (QuotientGroup.mk' kernelGroup) (QuotientGroup.mk'_surjective _) hnonab

theorem catalogSections_subgroup
    {G : Type*} [Group G] (hcatalog : HasCatalogSimpleSections G)
    (subgroup : Subgroup G) : HasCatalogSimpleSections subgroup := by
  intro sectionGroup kernelGroup hnormal hsimple hnonab
  let : kernelGroup.Normal := hnormal
  let : IsSimpleGroup (sectionGroup ⧸ kernelGroup) := hsimple
  let liftedGroup := Subgroup.map subgroup.subtype sectionGroup
  let liftedEquiv := sectionGroup.equivMapOfInjective subgroup.subtype subgroup.subtype_injective
  let liftedMap : liftedGroup →* sectionGroup ⧸ kernelGroup :=
    (QuotientGroup.mk' kernelGroup).comp liftedEquiv.symm.toMonoidHom
  exact catalog_simple_subgroup_surjective_image_order hcatalog liftedGroup liftedMap
    ((QuotientGroup.mk'_surjective _).comp liftedEquiv.symm.surjective) hnonab

theorem catalogSections_quotient
    {G : Type*} [Group G] (hcatalog : HasCatalogSimpleSections G)
    (normalGroup : Subgroup G) [normalGroup.Normal] :
    HasCatalogSimpleSections (G ⧸ normalGroup) :=
  catalogSections_surjective hcatalog (QuotientGroup.mk' normalGroup) (QuotientGroup.mk'_surjective _)

theorem catalog_simple_subgroup_order
    {G : Type*} [Group G] (hcatalog : HasCatalogSimpleSections G)
    (simpleGroup : Subgroup G) (hsimple : IsSimpleGroup simpleGroup)
    (hnonab : ∃ first second : simpleGroup, first * second ≠ second * first) :
    Nat.card simpleGroup ∈ knownSimpleOrders := by
  let : IsSimpleGroup simpleGroup := hsimple
  exact catalog_simple_subgroup_surjective_image_order hcatalog simpleGroup
    (MonoidHom.id simpleGroup) Function.surjective_id hnonab

end CFSG.RankThreeCoreUniqueness.Helpers
