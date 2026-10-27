module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.KD291Perf

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3

section CertificateInstances

theorem gammaStructureP_holds : GammaStructureP :=
  gammaStructureP_of_tables CFSG.LocalAnalysis.RankFourTheoremC.kdInndiagP5_holds
    CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds

end CertificateInstances

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3
