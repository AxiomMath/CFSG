module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcTw
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorusDefs

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.HardMathSupport.Timmesfeld.CrossChar


theorem langComponentsQuasisimple_excT (hTw : TwistedE6TrialityComponentsT) :
    LangComponentsQuasisimpleT .exc :=
  fun τ L _ _ p S a hT hTp ha1 i hk _ => excQuasisimpleAtT_of hTw τ L p S a hT hTp ha1 i hk

theorem langComponentsQuasisimple_exc_provedT : LangComponentsQuasisimpleT .exc :=
  langComponentsQuasisimple_excT twistedE6TrialityComponents_provedT

end CFSG.HardMathSupport.Timmesfeld.LangTorus
