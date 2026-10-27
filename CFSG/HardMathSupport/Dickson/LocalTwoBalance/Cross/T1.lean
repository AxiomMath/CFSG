module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidAssembly
public import CFSG.HardMathSupport.Timmesfeld.RootAut.Inner
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUProved
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwoDProved

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.HardMathSupport.Timmesfeld CFSG.HardMathSupport.Timmesfeld.CrossChar


theorem t1_pieces : LangTorus.LangComponentPieces :=
  ⟨LangTorus.langSubnormal_proved, RootAut.langComponentsQuasisimple_inner_holds,
    langComponentsQuasisimple_suN_proved, langComponentsQuasisimple_twoD_proved,
    LangTorus.langComponentsQuasisimple_exc_proved⟩

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
