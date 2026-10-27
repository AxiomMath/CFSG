module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.PairE7
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.PairPOFinal

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup


theorem hasPOmegaClassBMember_of_lieModel_e7 (hC2 : POmegaPlusCentreExpTwo)
    (hC4 : POmegaPlusNotLinUnit) {L Q : Type} [Group L] [Finite L] [Group Q] [Finite Q]
    [IsSimpleGroup Q] (π : L →* Q) (hπ : Function.Surjective π) (hk : π.ker ≤ center L)
    (h : CFSG.Blueprint.LieModel Q .E7 0 3 1) : HasPOmegaClassBMember L :=
  (hasPOmegaMember_of_lieModel_e7 h).hasPOmegaClassBMember_of_cover hC2 hC4 π hπ hk

theorem hasPOmegaClassBMember_of_lieModel_e7_quotient (hC2 : POmegaPlusCentreExpTwo)
    (hC4 : POmegaPlusNotLinUnit) {L : Type} [Group L] [Finite L] [IsSimpleGroup (L ⧸ center L)]
    (h : CFSG.Blueprint.LieModel (L ⧸ center L) .E7 0 3 1) : HasPOmegaClassBMember L :=
  hasPOmegaClassBMember_of_lieModel_e7 hC2 hC4 (QuotientGroup.mk' (center L))
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _).le h

end CFSG.OddStandard.HigherRank.F3
