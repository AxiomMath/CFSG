module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K37Lie
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K37ExcTits
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K37L34
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K37DefChar
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K37Alt
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K37Spor
public import CFSG.RankThree.PartTwo.Sec4.Census.Item43Narrow

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K37

open CFSG.Open


theorem kFactThreeSevenTwoThree_of_inputs (hR : K37Rest)
    (hSR : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hL28 : CFSG.AGLEmbedding.KFactCaseTwoNoTwoL28)
    (hK35 : CFSG.LocalAnalysis.AGL81TheoremCD.Section15.KFactThreeFiveInner)
    (hODC : CFSG.LocalAnalysis.UniquenessCase.UCK.K36OddDefChar)
    (hSpM : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers)
    (hK315 : CFSG.LocalAnalysis.UniquenessCase.UCK.K315Spor) :
    CFSG.LocalAnalysis.AGL81TheoremCD.Section15.KFactThreeSevenTwoThree := by
  refine kFactThreeSevenTwoThree_of_forall_goal fun X _ _ K E S h => ?_
  refine h.goal_of_catalog (fun d hd3 hd => ?_) (fun d hd3 hd => ?_) (fun n hn hφ => ?_)
    (fun s hφ => ?_)
  ·
    by_cases hO : K37Open K E
    · exact h.goal_of_open hR hO
    by_cases hL34 : AGL81C.IsL34Type ↥K
    · exact fun hSC => h.concl_of_l34 hL34 hSC
    by_cases hexc : (∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .A 1 q) ∨
        (∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧ d.1 = .B 3 q) ∨ d.1 = .tits
    · exact fun hSC => absurd (h.le_centralizer_of_exc hGA hL28 hK35 d hd hexc) hSC
    · exact (h.false_of_lie hSR hGA d hd3 hd hO hL34 hexc).elim
  ·
    by_cases hO : K37Open K E
    · exact h.goal_of_open hR hO
    exact fun hSC => absurd (h.le_centralizer_of_defChar
      (CFSG.RankThree.PartTwo.Sec4.Census.tripleCoverLie_of_griess hGA) hODC d hd3 hd hO) hSC
  ·
    by_cases hO : K37Open K E
    · exact h.goal_of_open hR hO
    exact h.goal_of_alternating hn hφ hO
  ·
    by_cases hO : K37Open K E
    · exact h.goal_of_open hR hO
    exact fun hSC => absurd (h.le_centralizer_of_spor hSpM hK315 hφ hO) hSC

end CFSG.LocalAnalysis.RankThreeUC.S15.K37
