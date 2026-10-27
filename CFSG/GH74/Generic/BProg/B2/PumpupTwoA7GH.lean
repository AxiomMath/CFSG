module

public import CFSG.GH74.Generic.BProg.B2.TwoA7TermG
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87TwoA7Final

public section

namespace CFSG.GH74.Generic.BProg.B2.SD.TwoA7TermG

open CFSG CFSG.GH74 CFSG.GH74.GLS


theorem pumpupTwoA7GH : PumpupTwoA7GH := by
  intro H _ _ _ _ L I s K₀ _ hGH hL hs hsI hIL hIc hK₀ hφ
  exact CFSG.GH74.GLS.Stage2.Signalizer.Odd87.pumpupTwoA7_of_ghList L I s hGH hL hs hsI hIL hIc
    hK₀ hφ

end CFSG.GH74.Generic.BProg.B2.SD.TwoA7TermG
