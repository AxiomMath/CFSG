module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFH0Wired
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.FFH0Final

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.AGLEmbeddingD2.Tits.MsidePrelim CFSG.AGLEmbedding CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

theorem ffH0Hyp_of_data (h : FFH0Data) : FFH0Hyp := by
  intro d G _ _ P M A H R Rbar K hc hstr hAll T hT hNT hU I hMN hcard hJM hSyl hperm hfam L hL
  obtain ⟨H₀, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    h d G P M A H R Rbar K hc hstr hAll T hT hNT hU I hMN hcard hJM hSyl hperm hfam L hL
  exact ⟨H₀, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩⟩

theorem ffGroupStep : FFGroupStep := ffGroupStep_of_h0 (ffH0Hyp_of_data ffH0Data)

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
