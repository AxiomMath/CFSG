module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.L62Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.NoncyclicCentre
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.AltTriple
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Spor
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Chev3
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.Final
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.OuterFixedMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.InnerFusionMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.LThreeEpsCase
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.L62Qrank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

section Tables


theorem gl83SmallRankLemma62At3_proved
    (G : Type) [Group G] [Finite G] :
    GL83SmallRankLemma62At3 G :=
  gl83SmallRankLemma62At3_of_kfacts
      (T29.gl83I291Three_of_families (T29.noncyclicCentreRank_of_tables
          (CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement)
          (CFSG.HardMathSupport.Timmesfeld.Coordinator.sporadicMultipliers_of_census
              CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds))
          T29.altTripleCoverAbelianBound_holds T29.t29Spor_holds T29.t29Chev3_holds
          (T29.Parrott.t29ChevOther_of_kfacts T29.Parrott.t29LThreeEpsCase_holds
              T29.Parrott.outerFixedE9_holds T29.Parrott.innerFusionE9Exc_holds)) (T29.noncyclicCentreRank_of_tables
              (CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement)
              (CFSG.HardMathSupport.Timmesfeld.Coordinator.sporadicMultipliers_of_census
                  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds))
      (kFactThreeComponentsQRank_of_catalog (T29.noncyclicCentreRank_of_tables
          (CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement)
          (CFSG.HardMathSupport.Timmesfeld.Coordinator.sporadicMultipliers_of_census
              CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds))
          (k3CatalogQCyc_of_lie
              (CFSG.HardMathSupport.Timmesfeld.Coordinator.sporadicMultipliers_of_census
                  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds)
              (k3CatalogQCycLie_of_table
                  (CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement)))) G

end Tables

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
