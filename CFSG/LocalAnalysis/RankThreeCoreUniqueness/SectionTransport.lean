module

public import CFSG.Foundations.KCoreOpen

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

theorem kProper_simple_surjective_image_order
    {G : Type*} [Group G] (hK : IsKProperByOrder G)
    (overgroup : Subgroup G) (hproper : overgroup ≠ ⊤)
    {Target : Type*} [Group Target] [IsSimpleGroup Target]
    (homomorphism : overgroup →* Target) (hsurjective : Function.Surjective homomorphism)
    (hnonab : ∃ first second : Target, first * second ≠ second * first) :
    Nat.card Target ∈ knownSimpleOrders :=
  CFSG.KCore.KProperNonab.catalogue_of_surjective_transfer knownSimpleOrders_isoTransfer hK
    overgroup hproper hnonab homomorphism hsurjective

theorem kProper_proper_subgroup_image_simple_subgroup_image_order
    {G : Type*} [Group G] (hK : IsKProperByOrder G)
    (overgroup : Subgroup G) (hproper : overgroup ≠ ⊤)
    {Image : Type*} [Group Image]
    (homomorphism : overgroup →* Image) (hsurjective : Function.Surjective homomorphism)
    (sectionGroup : Subgroup Image)
    {Target : Type*} [Group Target] [IsSimpleGroup Target]
    (sectionMap : sectionGroup →* Target) (hsectionSurjective : Function.Surjective sectionMap)
    (hnonab : ∃ first second : Target, first * second ≠ second * first) :
    Nat.card Target ∈ knownSimpleOrders :=
  ((CFSG.KCore.KProperNonab.kGroupNonab knownSimpleOrders_isoInvariant hK overgroup hproper
    ).of_surjective_transfer knownSimpleOrders_isoTransfer homomorphism hsurjective
    ).catalogue_of_surjective_transfer knownSimpleOrders_isoTransfer sectionGroup hnonab sectionMap
    hsectionSurjective

theorem kProper_proper_subgroup_surjective_image_isKProper
    {G : Type*} [Group G] (hK : IsKProperByOrder G)
    (overgroup : Subgroup G) (hproper : overgroup ≠ ⊤)
    {Image : Type*} [Group Image]
    (homomorphism : overgroup →* Image) (hsurjective : Function.Surjective homomorphism) :
    IsKProperByOrder Image :=
  ((CFSG.KCore.KProperNonab.kGroupNonab knownSimpleOrders_isoInvariant hK overgroup hproper
    ).of_surjective_transfer knownSimpleOrders_isoTransfer homomorphism hsurjective).kProperNonab

theorem kProper_proper_subgroup_isKProper
    {G : Type*} [Group G] (hK : IsKProperByOrder G)
    (overgroup : Subgroup G) (hproper : overgroup ≠ ⊤) : IsKProperByOrder overgroup :=
  kProper_proper_subgroup_surjective_image_isKProper hK overgroup hproper
    (MonoidHom.id overgroup) Function.surjective_id

theorem kProper_proper_subgroup_quotient_isKProper
    {G : Type*} [Group G] (hK : IsKProperByOrder G)
    (overgroup : Subgroup G) (hproper : overgroup ≠ ⊤)
    (normalGroup : Subgroup overgroup) [normalGroup.Normal] :
    IsKProperByOrder (overgroup ⧸ normalGroup) :=
  kProper_proper_subgroup_surjective_image_isKProper hK overgroup hproper
    (QuotientGroup.mk' normalGroup) (QuotientGroup.mk'_surjective _)

end CFSG.RankThreeCoreUniqueness.Helpers
