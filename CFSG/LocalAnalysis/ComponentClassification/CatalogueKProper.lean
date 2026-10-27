module

public import CFSG.Assembly.InCatalog

public section

namespace CFSG.ComponentClassification.CatalogueKProper

open CFSG.Assembly

theorem catalogue_of_equiv {G H : Type} [Group G] [Group H] (hcatalogue : InCatalog G)
    (equivalence : G ≃* H) : InCatalog H :=
  inCatalog_isoInvariant equivalence.symm hcatalogue

theorem catalogue_equiv_iff {G H : Type} [Group G] [Group H] (equivalence : G ≃* H) :
    InCatalog G ↔ InCatalog H :=
  ⟨fun hcatalogue => catalogue_of_equiv hcatalogue equivalence,
    fun hcatalogue => catalogue_of_equiv hcatalogue equivalence.symm⟩

theorem simple_quotient_of_surjective (G : Type) [Group G] (hK : KProper InCatalog G)
    (subgroup : Subgroup G) (hproper : subgroup ≠ ⊤) (simple : Type) [Group simple]
    [IsSimpleGroup simple] (hnonab : ∃ a b : simple, a * b ≠ b * a)
    (quotient : subgroup →* simple) (hsurjective : Function.Surjective quotient) :
    InCatalog simple :=
  KCore.KProperNonab.catalogue_of_surjective inCatalog_isoInvariant hK subgroup hproper hnonab
    quotient hsurjective

theorem simple_section_of_surjective (G : Type) [Group G] (hK : KProper InCatalog G)
    (subgroup : Subgroup G) (hproper : subgroup ≠ ⊤) (quotientType : Type) [Group quotientType]
    (quotient : subgroup →* quotientType) (hsurjective : Function.Surjective quotient)
    (quotientSubgroup : Subgroup quotientType) (simple : Type) [Group simple]
    [IsSimpleGroup simple] (hnonab : ∃ a b : simple, a * b ≠ b * a)
    (sectionQuotient : quotientSubgroup →* simple)
    (hsectionSurjective : Function.Surjective sectionQuotient) : InCatalog simple := by
  let preimage : Subgroup subgroup := quotientSubgroup.comap quotient
  let equivalence : preimage ≃* preimage.map subgroup.subtype :=
    preimage.equivMapOfInjective subgroup.subtype subgroup.subtype_injective
  exact simple_quotient_of_surjective G hK _ (KCore.map_subtype_ne_top hproper preimage) simple
    hnonab ((sectionQuotient.comp (quotient.subgroupComap quotientSubgroup)).comp
      equivalence.symm.toMonoidHom)
    ((hsectionSurjective.comp (quotient.subgroupComap_surjective _ hsurjective)).comp
      equivalence.symm.surjective)

theorem of_injective {G H : Type} [Group G] [Group H] (hK : KProper InCatalog G)
    (embedding : H →* G) (hinjective : Function.Injective embedding) : KProper InCatalog H :=
  KCore.KProperNonab.of_injective inCatalog_isoInvariant hK embedding hinjective

theorem of_surjective {G H : Type} [Group G] [Group H] (hK : KProper InCatalog G)
    (quotient : G →* H) (hsurjective : Function.Surjective quotient) : KProper InCatalog H :=
  KCore.KProperNonab.of_surjective inCatalog_isoInvariant hK quotient hsurjective

theorem subgroup {G : Type} [Group G] (hK : KProper InCatalog G) (H : Subgroup G) :
    KProper InCatalog H :=
  of_injective hK H.subtype H.subtype_injective

theorem quotient {G : Type} [Group G] (hK : KProper InCatalog G) (N : Subgroup G) [N.Normal] :
    KProper InCatalog (G ⧸ N) :=
  of_surjective hK (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

theorem section_closed {G : Type} [Group G] (hK : KProper InCatalog G) (H : Subgroup G)
    (N : Subgroup H) [N.Normal] : KProper InCatalog (H ⧸ N) :=
  quotient (CatalogueKProper.subgroup hK H) N

theorem of_equiv {G H : Type} [Group G] [Group H] (hK : KProper InCatalog G)
    (equivalence : G ≃* H) : KProper InCatalog H :=
  of_surjective hK equivalence.toMonoidHom equivalence.surjective

theorem section_closed_of_equiv {G Y : Type} [Group G] [Group Y] (hK : KProper InCatalog G)
    (H : Subgroup G) (N : Subgroup H) [N.Normal] (equivalence : (H ⧸ N) ≃* Y) :
    KProper InCatalog Y :=
  of_equiv (section_closed hK H N) equivalence

end CFSG.ComponentClassification.CatalogueKProper
