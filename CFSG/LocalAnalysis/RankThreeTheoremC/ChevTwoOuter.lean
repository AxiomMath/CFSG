module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoOuterParts
public import CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoOuterD4
public import CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoOuterU3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding (IsChevTwoOuterIndex KFactChevTwoOuterGen)
open CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoOuter

theorem kFactChevTwoOuterNormal : KFactChevTwoOuterNormal := by
  intro d hd S
  rcases (isChevTwoOuterIndex_iff d).mp hd with ⟨q, hq, -, hd'⟩ | ⟨q, hq, -, hd'⟩ |
    ⟨q, -, -, hd'⟩
  · exact (isPByAbelian_outer_trialityD4 d q hq hd' 3).normal_sylow S
  · exact (isPByAbelian_outer_trialityD4 d q hq hd' 3).normal_sylow S
  · exact (isPByAbelian_outer_twistedA_two d q hd').normal_sylow S

end CFSG.LocalAnalysis.RankThreeTheoremC
