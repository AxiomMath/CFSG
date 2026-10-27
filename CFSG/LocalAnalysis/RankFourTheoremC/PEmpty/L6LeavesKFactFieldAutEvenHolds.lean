module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenLBAll
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenOLAll
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.LieOver.Reduction

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

theorem kFactFieldAutEven_holds :
    KFactFieldAutEven :=
  KFAE.kFactFieldAutEven_of_props CFSG.RankThree.PartOne.TCB.tauCetiCatalogBridge
      CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
      (CFSG.AGLEmbedding.not_dvd_card_outer_sporadic
          CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group)
      CFSG.Sporadic.Schreier.Tits.AT_Tits_model_Schreier
      CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
      CFSG.AGLEmbedding.OuterSylow.not_dvd_divisor_of_cyclic
      CFSG.HardMathSupport.Lang.Coordinator.outerFixedOrderBoundCyc_holds KFAE.fixedLowerBoundAt_all
      (KFAE.overgroupLocalAt_all CFSG.Quasithin.LieOver.asLieTwo_holds.1
          CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
