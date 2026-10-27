module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.BetaBase
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.PushUp

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsidePrelim

open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2

theorem d2L34BetaPushUpCover
    (hFF : CitedFFL34BestOffender) : D2L34BetaPushUpCover := by
  intro d G _ _ P M A H R Rbar K hc hstr V hV hAV
  exact D2L34BetaConf.exists_char_cover hFF hc hstr hV hAV

theorem d2L34BetaPushUpCoverSyl
    (hFF : CitedFFL34BestOffender) : D2L34BetaPushUpCoverSyl := by
  intro d G _ _ P M A H R Rbar K hc hstr T hT
  exact D2L34BetaConf.exists_char_cover_syl hFF hc hstr hT

end CFSG.AGLEmbeddingD2.Tits.MsidePrelim
