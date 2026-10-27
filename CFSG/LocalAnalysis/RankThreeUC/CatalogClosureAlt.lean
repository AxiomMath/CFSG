module

public import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureOddBasic
import CFSG.RankThree.PartTwo.Census.Alternating
import CFSG.LocalAnalysis.SectionRank.Alternating

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.RankThree.PartTwo.Census CFSG.RankThree.PartOne.Census3

variable {G : Type} [Group G] [Finite G]

theorem Standing.false_of_item5 (hS : Standing G) (h : ThmThreeItem5 G) : False := by
  obtain ⟨n, -, -, ⟨e⟩⟩ := h
  rcases le_or_gt n 8 with h8 | h9
  · exact hS.false_of_pRank_le_two e fun r hr hr2 =>
      CFSG.SectionRank.pRank_alternating_le_two h8 hr hr2
  · exact hS.false_of_not_isCharTwoType e (not_isCharTwoType_alternating h9)

end CFSG.LocalAnalysis.RankThreeUC
