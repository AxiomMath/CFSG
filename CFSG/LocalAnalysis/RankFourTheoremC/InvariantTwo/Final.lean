module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.MainC
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CatalogSchreier
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProof

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

section CertificateInstances

theorem invariantTwoSylowOfD1Rank4_of_i294Two (hI : GL83I294Two) :
    InvariantTwoSylowOfD1Rank4 := invariantTwoSylowOfD1Rank4_of_kfactsC
    (kFactLemma212Ge_four gl83PElementCentralizerRank_holds gl83OutDiagPowerMap_holds)
    (kFactLemma213RedC_four_of_rank4 (GL83I294TwoFour.of_two hI) CFSG.AGLEmbedding.kFactCatalogSchreier).toGeC

end CertificateInstances

end CFSG.LocalAnalysis.RankFourTheoremC
