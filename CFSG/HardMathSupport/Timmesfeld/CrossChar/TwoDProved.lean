module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwoDFour
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighMain

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.HardMathSupport.Timmesfeld.LangTorus


theorem langComponentsQuasisimple_twoD_proved : LangComponentsQuasisimple .twoD :=
  langComponentsQuasisimple_twoD_of_high e6FixDNAll_proved twoDHighComponents_proved

theorem langComponentsQuasisimpleT_twoD_proved : LangComponentsQuasisimpleT .twoD :=
  langComponentsQuasisimpleT_twoD_of_high e6FixDNAll_proved twoDHighComponentsT_proved

end CFSG.HardMathSupport.Timmesfeld.CrossChar
