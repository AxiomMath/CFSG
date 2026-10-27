module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenTwelveOneOf
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenTwelveRanksLeOrth
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenTwelveRanksLeUni

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

theorem kFactTwelveRanksLe_of_U (h : KFactTwelveRanksLeU) : KFactTwelveRanksLe := by
  intro Y _ _
  refine ⟨fun hY => ?_, TwelveRanksLe.four_le_pRank_of_isLieOver_orth⟩
  rcases hY with hD | hTD | hA
  · exact TwelveRanksLe.exists_isElemAbelian_card_nine_of_isLieOver_orth (Or.inl hD)
  · exact TwelveRanksLe.exists_isElemAbelian_card_nine_of_isLieOver_orth (Or.inr hTD)
  · exact h Y hA

theorem kFactTwelveRanksLe_holds :
    KFactTwelveRanksLe :=
  kFactTwelveRanksLe_of_U kFactTwelveRanksLeU_holds

end CFSG.LocalAnalysis.RankThreeTheoremC
