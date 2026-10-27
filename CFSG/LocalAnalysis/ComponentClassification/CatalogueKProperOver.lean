module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.ComponentClassification.CatalogueKProperOver

open CFSG.Assembly

variable {C : GroupProp}

theorem kProper_of_surjective (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    {G H : Type} [Group G] [Group H] (hK : KProper C G) (quotient : G →* H)
    (hsurjective : Function.Surjective quotient) : KProper C H :=
  CFSG.KCore.KProperNonab.of_surjective hC hK quotient hsurjective

theorem kProper_quotient (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    {G : Type} [Group G] (hK : KProper C G) (N : Subgroup G) [N.Normal] :
    KProper C (G ⧸ N) :=
  kProper_of_surjective hC hK (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

end CFSG.ComponentClassification.CatalogueKProperOver
