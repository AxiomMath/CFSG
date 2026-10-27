module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Chev
public import CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoInnerRankChev
import CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoInnerRankD4
import CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoInnerRankSp
import CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoInnerRankUnitary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding (IsChevTwoInnerIndex)
open ChevTwoInnerRank TauCeti

@[expose] def InnerCoversFour : Prop :=
  ∀ d : ValidLieTypeIndex, IsChevTwoInnerIndex d → CentralCoverFour (CFSGIndex.lie d).Group

theorem kFactChevTwoInnerRank_of_innerCoversFour (h : InnerCoversFour) :
    KFactChevTwoInnerRank := by
  intro d hd K _ _ _ ⟨e⟩ _ _ T
  exact four_le_pRank_sylow_of_centralCoverFour (h d hd) e T

theorem innerCoversFour_of_certificates : InnerCoversFour := by
  rintro ⟨c, hv⟩ ⟨q, hq2, hq1, hc⟩
  rcases hc with hc | hc | hc | hc | hc | hc <;> simp only at hc <;> subst hc
  · exact centralCoverFour_B4Two q hv hq2 hq1
  · exact centralCoverFour_twistedA4Two q hv hq2 hq1
  · exact centralCoverFour_twistedA5Two q hv hq2 hq1
  · exact centralCoverFour_D4Two q hv hq2 hq1
  · exact centralCoverFour_F4Two q hv hq2 hq1
  · exact centralCoverFour_E6Two q hv hq2 hq1

theorem kFactChevTwoInnerRank_of_certificates : KFactChevTwoInnerRank :=
  kFactChevTwoInnerRank_of_innerCoversFour innerCoversFour_of_certificates

end CFSG.LocalAnalysis.RankThreeTheoremC
