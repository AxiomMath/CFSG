module

public import CFSG.HardMathSupport.Timmesfeld.RootAut.Main
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerSmall

public section

namespace CFSG.HardMathSupport.Timmesfeld.RootAut

open CFSG.HardMathSupport.Timmesfeld.LangTorus

theorem langComponentsQuasisimple_inner_holds :
    LangComponentsQuasisimple .inner :=
  langComponentsQuasisimple_inner_of_rootAutIsWeyl rootAutIsWeyl_holds

end CFSG.HardMathSupport.Timmesfeld.RootAut
