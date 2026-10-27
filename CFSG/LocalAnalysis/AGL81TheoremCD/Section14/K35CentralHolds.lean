module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.K35CentralMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.TripleCoverWideHolds
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.NoncyclicCentre
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.ScopeBFrontier

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.K35Central


theorem kFactThreeFiveCentral_holds :
    CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFactThreeFiveCentral :=
  kFactThreeFiveCentral_of_lists
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.TripleCover.kFactAlphaListM3Wide_holds
    (RankThreeTheoremC.KFactProofs.T29.noncyclicCentreRank_of_tables
        (CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement)
        (CFSG.HardMathSupport.Timmesfeld.Coordinator.sporadicMultipliers_of_census
            CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds))

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.K35Central
