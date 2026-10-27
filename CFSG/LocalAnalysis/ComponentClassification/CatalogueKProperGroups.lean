module

public import CFSG.Foundations.Catalog
public import CFSG.Open.Defs

public section

namespace CFSG.ComponentClassification.CatalogueKProper

open CFSG.Assembly

theorem simple_image_of_surjective (G : Type) [Group G] [Finite G]
    (hK : KProper InCatalog G) (subgroup : Subgroup G) (hproper : subgroup ≠ ⊤)
    (simple : Type) [Group simple] [IsSimpleGroup simple] (quotient : subgroup →* simple)
    (hsurjective : Function.Surjective quotient) : InCatalog simple :=
  (KCore.KProperNonab.kProperAllSimple inCatalog_isoInvariant inCatalog_containsAbelianSimple
    hK).catalogue_of_surjective inCatalog_isoInvariant subgroup hproper quotient hsurjective

theorem proper_subgroup_isKGroup {G : Type} [Group G] [Finite G] (hK : KProper InCatalog G)
    (H : Subgroup G) (hproper : H ≠ ⊤) : CFSG.IsKGroup H :=
  KCore.KProperNonab.kGroupAllSimple inCatalog_isoInvariant inCatalog_containsAbelianSimple hK H
    hproper

theorem isKProper_of_kProper {G : Type} [Group G] [Finite G] (hK : KProper InCatalog G) :
    CFSG.IsKProper G :=
  fun H hproper => proper_subgroup_isKGroup hK H hproper

theorem simple_quotient_of_isKGroup {G : Type} [Group G] (hK : CFSG.IsKGroup G)
    (H : Subgroup G) (simple : Type) [Group simple] [IsSimpleGroup simple]
    (quotient : H →* simple) (hsurjective : Function.Surjective quotient) : InCatalog simple :=
  hK.inCatalog_of_surjective H quotient hsurjective

theorem kProper_of_isKProper {G : Type} [Group G] (hK : CFSG.IsKProper G) :
    KProper InCatalog G :=
  KCore.KProperAllSimple.kProperNonab inCatalog_isoInvariant hK

theorem isKProper_iff_kProper {G : Type} [Group G] [Finite G] :
    CFSG.IsKProper G ↔ KProper InCatalog G :=
  ⟨kProper_of_isKProper, isKProper_of_kProper⟩

theorem open_isKProper_iff {G : Type} [Group G] :
    CFSG.Open.IsKProper G ↔ KProper InCatalog G := Iff.rfl

theorem proper_subgroup_open_isKGroup {G : Type} [Group G] (hK : KProper InCatalog G)
    (H : Subgroup G) (hproper : H ≠ ⊤) : CFSG.Open.IsKGroup H :=
  KCore.KProperNonab.kGroupNonab inCatalog_isoInvariant hK H hproper

end CFSG.ComponentClassification.CatalogueKProper
