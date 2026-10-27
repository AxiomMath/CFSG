module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.GenericKFactsFrontier
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.GenericKFactsOpen
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleTowerAssembly
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Tables
public import CFSG.LocalAnalysis.GL83PartI.I_24_3.IsoPlaneMain
public import CFSG.LieType.SeitzGeneration.SeitzOuterLowNProof
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.ComponentPCoreThree
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SchurRankHolds
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.TripleCoverWideHolds
import all CFSG.Blueprint.NativeSporadic
public import CFSG.HardMathSupport.Solomon.Coordinator.I19DefCharHolds
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossLargePrimeMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossRankTwoG2
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossRankTwoRee
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossRankTwoSz
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossRankTwoTits
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossRankTwoTriality
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeExc
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeLinFour
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeLinSix
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeOmMinusMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeOmSeven
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeRankThreeAssembly
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeSpMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeUniPSU67
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294KDOutMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294LayerKD
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294SporJ3
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294SporRank
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294SporRankFive

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth

open CFSG.LieType.SeitzGeneration

set_option linter.unusedSectionVars true

theorem gl83GenericKFacts_unconditional
    :
    CFSG.Yardstones.M9cbf837c48cf.GL83GenericKFactsStatement :=
  gl83GenericKFacts_of_open (CyclicOuter.seitzOuterRankOne_of_lowN seitzOuterLowN_holds)
    WeakClosure.crossCharTagsRest_holds
    (kFactComponentPCoreThree_of_general GL83.I243.gl83ComponentPCoreTrivial_holds)
    (Bal3.bal3KFacts_of_open' SchurRank.schurMultiplierRankFact_holds
      TripleCover.kFactAlphaListM3Wide_holds
      CFSG.AGLEmbedding.abelianSylowDatum_ON_three
      (Bal3.input29_4Rank3_of_inputs
          CFSG.HardMathSupport.Solomon.Coordinator.defCharInnerCoreFree_holds
          Bal3.kDOutDerived_holds Bal3.i294OuterDiag_holds
          (CFSG.AGLEmbedding.not_dvd_card_outer_sporadic
              CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group)
          (Bal3.sporadicCentralizerPPart_of_three Bal3.sporadicThreeRankThree_holds
              Bal3.j3ThreeCentralizer_holds)
          (Bal3.i294InnerLieCross_of_inputs Bal3.i294CrossLargePrime_holds
              (Bal3.i294CrossThreeRankThree_of_models Bal3.i294CrossModelPSL4_holds
                  Bal3.i294CrossModelPSL67_holds Bal3.i294CrossModelPSU4_holds
                  Bal3.i294CrossModelPSU67_holds Bal3.i294CrossModelPSp6_holds
                  Bal3.i294CrossModelPOmega7_holds Bal3.i294CrossModelPOmegaMinus4_holds)
              (Bal3.I294CrossThreeRankTwo.of_families Bal3.i294CrossThreeRankTwoOn_G2
                  Bal3.i294CrossThreeRankTwoOn_ReeF4 Bal3.i294CrossThreeRankTwoOn_Tits
                  (Bal3.I294CrossThreeRankTwo.rest_of_families Bal3.i294CrossThreeRankTwoSz_holds
                      Bal3.i294CrossThreeRankTwoTriality_holds Bal3.i294CrossThreeRankTwoExc_holds
                      Bal3.i294CrossThreeRankTwoClassical_holds))) Bal3.i294InnerLieLayer_holds))
    AlmostSimple.almostSimplePartA_holds almostSimplePartBRankTwo_holds

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth
