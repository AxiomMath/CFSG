module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAll
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.G2LongFrame
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwoDProved
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcTorus
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerTorus

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.RootAut

theorem langComponentsQuasisimpleT_suN_proved : LangComponentsQuasisimpleT .suN :=
  langComponentsQuasisimpleT_suN g2LongA2Frame_proved

theorem langComponentsQuasisimpleT_all (k : TwistKind) : LangComponentsQuasisimpleT k := by
  cases k
  · exact langComponentsQuasisimple_inner_holdsT
  · exact langComponentsQuasisimpleT_suN_proved
  · exact langComponentsQuasisimpleT_twoD_proved
  · exact langComponentsQuasisimple_exc_provedT

end CFSG.HardMathSupport.Timmesfeld.LangTorus

end
