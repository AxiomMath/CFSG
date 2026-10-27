module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.LiftQ
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.CatalogQLie
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.K2Core
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.NoncyclicCentre
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.AltTriple
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Spor
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Chev3
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.InnDiagRank
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.Lemma121
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZAction628.Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZAction629.Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerActionFinal
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.RankTwoUniq.K1RedMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.RankTwoUniq.K1CoreMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell.AvoidMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813.Main
public import CFSG.GroupTheory.HuppertProduct.RankBound
public import CFSG.LocalAnalysis.RankThreeUC.TheoremDThreeConstrained
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.Final
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.OuterFixedMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.InnerFusionMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.LThreeEpsCase
public import CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps.Holds

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

section Assembly


theorem gl83SmallRankKFacts_holds
    :
    SmallRankConstraintKFact3 ∧ KFactSylowNormalizerIrreducible ∧ KFactAbelianSylowRankThree ∧
      KFactZAction628 ∧ KFactZAction629 ∧ KFactOutThreePrimeSimple ∧ KFactRankTwoUniqueness ∧
      KFactRankThreeStructure ∧ KFactCampbell ∧ KFactLemma2813 ∧
      CFSG.LocalAnalysis.RankThreeUC.KFactHuppertProductThree := by
  have hT : T29.GL83I291Three := T29.gl83I291Three_of_families (T29.noncyclicCentreRank_of_tables
      (CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement)
      (CFSG.HardMathSupport.Timmesfeld.Coordinator.sporadicMultipliers_of_census
          CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds))
    T29.altTripleCoverAbelianBound_holds T29.t29Spor_holds T29.t29Chev3_holds
    (T29.Parrott.t29ChevOther_of_kfacts T29.Parrott.t29LThreeEpsCase_holds
        T29.Parrott.outerFixedE9_holds T29.Parrott.innerFusionE9Exc_holds)
  have h2316 : CFSG.HardMathSupport.Solomon.Coordinator.Input23_16Three :=
    HardMathSupport.Solomon.Coordinator.input23_16Three_of_withX
        (HardMathSupport.Solomon.Coordinator.bglFieldGenerationWithXThree_of_pair
            CFSG.HardMathSupport.Solomon.Coordinator.bglFieldPairGeneration_holds
            CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps.bglFieldGenerationWithXOffEps_holds)
        HardMathSupport.Solomon.Coordinator.field3Structure_holds
  refine ⟨K3.smallRankConstraintKFact3_of_core (T29.kfactConstraintCore_of_T29 hT)
      (K3.k3LiftThree_of_parts
          (K3.k3CatalogQ_of_lie
              (CFSG.HardMathSupport.Timmesfeld.Coordinator.sporadicMultipliers_of_census
                  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds)
              (K3.k3CatalogQLie_of_table
                  (CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement)))
          K3.k3LiftQ_holds),
    SmallRank.kFactSylowNormalizerIrreducible_holds, SmallRank.kFactAbelianSylowRankThree_holds,
    SmallRank.ZA628.kFactZAction628_holds, SmallRank.ZA629.kFactZAction629_holds,
    SmallRank.kFactOutThreePrimeSimple_of_innerAction Stroth.InnerAction.kFactInnerAction_holds,
        RankTwoUniq.kFactRankTwoUniqueness_of_core RankTwoUniq.k1Core_holds,
    K2.kfactRankThreeStructure_of_core
      (T29.kfactRankThreeCore_of_T29 hT T29.innDiagRankTwo_holds h2316),
    Campbell.kFactCampbell_of_asC134Weak CFSG.Quasithin.MS93.burnsideC134w_corrOneWeak,
    Lemma2813.kFactLemma2813_holds, ?_⟩
  exact fun _ _ _ _ _ _ _ hW hA hB hAc hBc hprod hEW hE =>
    CFSG.GroupTheory.HuppertProduct.card_ne_twentySeven_of_product hW hA hB hAc hBc hprod hEW hE.2

end Assembly

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
