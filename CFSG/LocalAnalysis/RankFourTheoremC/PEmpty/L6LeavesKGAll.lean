module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGFinal
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL613BMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGAltSixFactMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGFiveProved
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGNonMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGSixMain

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

section KFacts


theorem stepKGroupCore_of_kfacts (hKF : KFact64iiL) (hKD : KD291a3) (hr : KFact613rankP)
    (hAutO : KFactAutAltOrder) (hAutE : KFactAutAltEmbed) (h2024 : KG2024)
    (h2401 : KFact2401Three) (h2715 : KFact2715) (h131 : KFact131) (hpc : KFactParabolicCover)
    (hNC : KGNoncycCent) (hT : KGTransvCent) (h241 : KFact2401ThreeOmega) : StepKGroupCore :=
  stepKGroupCore_of_inputs hKF (kGL613b_of_inputs hKD hr) hAutO hAutE h2024 h2401 kGAltSix_holds
    h2715 h131 hpc kgStep5Sylow_holds (kgStep6Noncyc_of_inputs hNC) (kgStep6Cyc_of_inputs hT h241)

end KFacts

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
