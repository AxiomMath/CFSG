module

public import CFSG.LocalAnalysis.RankFourTheoremC.RelativePair.Main
public import CFSG.LocalAnalysis.RankFourTheoremC.RelativePair.ZJGe
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProof
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleTowerAssembly
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.GenericKFactsFrontier

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

section CertificateInstances


theorem kFactAlmostSimpleRankTwo_holds
    : RankThreeTheoremC.KFactAlmostSimpleRankTwo :=
  RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.kFactAlmostSimpleRankTwo_of_parts
    RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.almostSimplePartA_holds
    (RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.almostSimplePartB_of_rankTwo
      RankThreeTheoremC.KFactProofs.Stroth.almostSimplePartBRankTwo_holds)

theorem relativePairExclusionOfD1Rank4_holds
    : RelativePairExclusionOfD1Rank4 :=
  relativePairExclusionOfD1Rank4_of_kfacts
      (kFactLemma212Ge_four gl83PElementCentralizerRank_holds gl83OutDiagPowerMap_holds)
      kFactZJFactorizationGe_holds kFactAlmostSimpleRankTwo_holds

end CertificateInstances

end CFSG.LocalAnalysis.RankFourTheoremC
