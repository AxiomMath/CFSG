module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29Final3
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29ExcRankE7Final
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29ExcRankE8Holds

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

section CertificateInstances


theorem invariantTwoSylowOfD1Rank4_holds : InvariantTwoSylowOfD1Rank4 :=
  invariantTwoSylowOfD1Rank4_of_e7_e8
      (crossE7SevenSplit_of_rank RankThreeTheoremC.KFactProofs.Stroth.Bal3.i294CrossLargePrime_holds
          crossRankE7SevenSplit_holds)
      (crossE8FiveFour_of_rank RankThreeTheoremC.KFactProofs.Stroth.Bal3.i294CrossLargePrime_holds
          crossRankE8FiveFour_holds)

end CertificateInstances

end CFSG.LocalAnalysis.RankFourTheoremC
