module

public import CFSG.Assembly.Defs
public import CFSG.Foundations.KCoreOpen

public section

open CFSG.Open

namespace CFSG.ComponentClassification.KProper

theorem of_injective {G H : Type*} [Group G] [Group H] (hK : IsKProperByOrder G)
    (embedding : H →* G) (hinjective : Function.Injective embedding) : IsKProperByOrder H :=
  hK.of_injective embedding hinjective

theorem of_surjective {G H : Type*} [Group G] [Group H] (hK : IsKProperByOrder G)
    (quotient : G →* H) (hsurjective : Function.Surjective quotient) : IsKProperByOrder H :=
  hK.of_surjective quotient hsurjective

theorem subgroup {G : Type*} [Group G] (hK : IsKProperByOrder G) (subgroup : Subgroup G) :
    IsKProperByOrder subgroup :=
  of_injective hK subgroup.subtype subgroup.subtype_injective

theorem quotient {G : Type*} [Group G] (hK : IsKProperByOrder G) (normalSubgroup : Subgroup G)
    [normalSubgroup.Normal] : IsKProperByOrder (G ⧸ normalSubgroup) :=
  of_surjective hK (QuotientGroup.mk' normalSubgroup)
    (QuotientGroup.mk'_surjective normalSubgroup)

theorem section_closed {G : Type*} [Group G] (hK : IsKProperByOrder G) (subgroup : Subgroup G)
    (normalSubgroup : Subgroup subgroup) [normalSubgroup.Normal] :
    IsKProperByOrder (subgroup ⧸ normalSubgroup) :=
  quotient (CFSG.ComponentClassification.KProper.subgroup hK subgroup) normalSubgroup

theorem of_equiv {G H : Type*} [Group G] [Group H] (hK : IsKProperByOrder G)
    (equivalence : G ≃* H) : IsKProperByOrder H :=
  of_surjective hK equivalence.toMonoidHom equivalence.surjective

end CFSG.ComponentClassification.KProper
