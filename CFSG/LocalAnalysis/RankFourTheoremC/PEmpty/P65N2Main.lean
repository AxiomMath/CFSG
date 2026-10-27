module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65N2Beta
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713SMain

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

theorem kFactP65Rank4AB_of_beta (hβ : KFactBetaStructure) : KFactP65Rank4AB := by
  intro A _ _ p P X x z f Fs R hpl _ hcase hf hf2 hfp hF _ hRN hRp hRidx hR4 hcyc
  by_cases hcon : HasPrimeConstraint (G := ↥X) p
  · exact P65N2.p65N2_alpha hpl hcon hf hf2 hfp hF hRN hR4 hcyc
  · rcases hcase with hcon' | hnuniq
    · exact absurd hcon' hcon
    · exact P65N2.p65N2_beta hβ hpl hcon hnuniq hf hf2 hfp hF hRN hRp hRidx hcyc

theorem kFactP65Rank4AB_holds
    : KFactP65Rank4AB :=
  kFactP65Rank4AB_of_beta (kFactBetaStructure_holds K713S.kFactSylowSplit_holds)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
