module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbSimpleBQ
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbSimpleRes
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbSimpleDefs

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem kFactChevGraphOrbitSimple_of_cases
    (hcases : ∀ (Y : Type) [Group Y] [Finite Y], IsSimpleGroup Y → IsChevTwo Y →
      Core.HasBQGraph Y ∨ ResidualGraph Y) :
    KFactChevGraphOrbitSimple := by
  intro Y _ _ L R P hL hC hRN hR2 hSyl hMin hnP
  rcases hcases ↥L hL hC with hG | hG
  · exact gOrbConclS_of_hasBQGraph hL hG hRN hR2 hSyl hMin hnP
  · exact gOrbConclS_of_residualGraph hL hG hRN hR2 hSyl hMin hnP

end CFSG.AGLEmbeddingD2.Tits.GN516
