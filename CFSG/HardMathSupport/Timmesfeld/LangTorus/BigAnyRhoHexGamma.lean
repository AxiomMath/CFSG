module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyRhoHex
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwistedLineFix

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar

set_option linter.unusedSectionVars false


variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem LangSetup.hexGroupInGamma_of_hexStep_E6 (S : LangSetup Tag.E6 L p) (h : S.HexStep)
    (hAlg : S.IsAlgebraic) (hq3 : 3 ≤ S.D.q) : S.HexGroupInGamma :=
  fun _ hγ => twistedLine_hexGroup_le S hAlg hq3 h.rel6 hγ

end CFSG.HardMathSupport.Timmesfeld.LangTorus
