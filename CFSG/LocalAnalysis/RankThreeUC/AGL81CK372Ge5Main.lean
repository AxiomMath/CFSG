module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CK372Ge5Lie
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CK372Ge5Exc
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CK372Ge5DefChar
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CK372Ge5Alt
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CK372Ge5Spor
public import CFSG.LieType.SeitzGeneration.SeitzStatus
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36ODCCent
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TableComplete
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporPairs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.K372Ge5

section Inputs


theorem kFactThreeSevenTwoGe5_of_inputs (hSR : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSz : CFSG.AGLEmbedding.KFactCaseTwoNoTwoSz32)
    (hODC : CFSG.LocalAnalysis.UniquenessCase.UCK.OddDefCharCentralizer)
    (hSpM : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers)
    (hK : CFSG.LocalAnalysis.UniquenessCase.UCK.K315Spor)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hBr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hTab : CFSG.HardMathSupport.Solomon.Coordinator.SporadicP2Table) :
    KFactThreeSevenTwoGe5 := by
  refine kFactThreeSevenTwoGe5_of_forall_goal fun X _ _ p K E S h => h.goal_of_catalog ?_ ?_ ?_ ?_
  · intro d hdp hd hSC
    by_cases hnd : CFSG.AGLEmbeddingD2.IsD2SeitzException p d.1
    · exact absurd (h.le_centralizer_of_exc hGA hSz d hd hnd) hSC
    · exact (h.false_of_lie hSR hGA d hdp hd hnd).elim
  · intro d hdp hd hSC
    exact absurd (h.le_centralizer_of_defChar hGA hODC d hdp hd) hSC
  · intro n hn hφ hSC
    obtain ⟨φ⟩ := hφ
    exact (h.false_of_alt hn φ hSC).elim
  · intro s hs
    exact h.goal_of_spor hSpM hK hOut hBr hTab hs

end Inputs

section Holds


theorem kFactThreeSevenTwoGe5_holds : KFactThreeSevenTwoGe5 :=
  kFactThreeSevenTwoGe5_of_inputs CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds
    CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
    CFSG.AGLEmbedding.kFactCaseTwoNoTwoSz32
    CFSG.LocalAnalysis.UniquenessCase.UCK.oddDefCharCentralizer_holds
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds
    CFSG.LocalAnalysis.UniquenessCase.UCK.k315Spor_holds
    CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    CFSG.HardMathSupport.Solomon.Coordinator.sporadicP2Table_holds

end Holds

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.K372Ge5
