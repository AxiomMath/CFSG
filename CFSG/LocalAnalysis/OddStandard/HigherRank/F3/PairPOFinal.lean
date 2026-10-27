module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.PairPOFamilies
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.PairPOLift
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.PairPOMember

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG CFSG.Open

theorem HasPOmegaMember.hasPOmegaClassBMember_of_cover (hC2 : POmegaPlusCentreExpTwo)
    (hC4 : POmegaPlusNotLinUnit) {L Q : Type} [Group L] [Finite L] [Group Q] [Finite Q]
    (π : L →* Q) (hπ : Function.Surjective π) (hk : π.ker ≤ center L) (h : HasPOmegaMember Q) :
    HasPOmegaClassBMember L :=
  (h.lift hC2 π hπ hk).hasPOmegaClassBMember hC4

theorem hasPOmegaClassBMember_of_lieModel_pomega (hC2 : POmegaPlusCentreExpTwo)
    (hC4 : POmegaPlusNotLinUnit) {L Q : Type} [Group L] [Finite L] [Group Q] [Finite Q]
    [IsSimpleGroup Q] (π : L →* Q) (hπ : Function.Surjective π) (hk : π.ker ≤ center L)
    {τ : StatedLieTag} {n : ℕ}
    (hτ : (τ = .POmegaOdd ∧ 4 ≤ n) ∨ (τ = .POmegaPlus ∧ 5 ≤ n) ∨ (τ = .POmegaMinus ∧ 5 ≤ n))
    (h : CFSG.Blueprint.LieModel Q τ n 3 1) : HasPOmegaClassBMember L :=
  (hasPOmegaMember_of_lieModel_pomega hτ h).hasPOmegaClassBMember_of_cover hC2 hC4 π hπ hk

theorem hasPOmegaClassBMember_of_lieModel_pomega_quotient (hC2 : POmegaPlusCentreExpTwo)
    (hC4 : POmegaPlusNotLinUnit) {L : Type} [Group L] [Finite L] [IsSimpleGroup (L ⧸ center L)]
    {τ : StatedLieTag} {n : ℕ}
    (hτ : (τ = .POmegaOdd ∧ 4 ≤ n) ∨ (τ = .POmegaPlus ∧ 5 ≤ n) ∨ (τ = .POmegaMinus ∧ 5 ≤ n))
    (h : CFSG.Blueprint.LieModel (L ⧸ center L) τ n 3 1) : HasPOmegaClassBMember L :=
  hasPOmegaClassBMember_of_lieModel_pomega hC2 hC4 (QuotientGroup.mk' (center L))
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _).le hτ h

end CFSG.OddStandard.HigherRank.F3
