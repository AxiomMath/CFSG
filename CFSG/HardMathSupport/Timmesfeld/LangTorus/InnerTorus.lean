module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerSmall
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorusDefs
public import CFSG.HardMathSupport.Timmesfeld.RootAut.Main

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KE
open scoped commutatorElement

set_option linter.unusedSectionVars false


theorem langComponentsQuasisimple_inner_of_smallT (hW : RootAutIsWeyl)
    (hsmall : SmallFieldInner) :
    LangComponentsQuasisimpleT .inner := fun _ _ _ _ _ S _ hT hTp ha1 i hkind hbig =>
  rationalComponent_quasisimple_innerT S hW hsmall hT hTp ha1 i hkind hbig

theorem langComponentsQuasisimple_inner_of_b2T (hW : RootAutIsWeyl) (hB2 : B2Two) :
    LangComponentsQuasisimpleT .inner :=
  langComponentsQuasisimple_inner_of_smallT hW (smallFieldInner_of_b2 hB2)

theorem langComponentsQuasisimple_inner_of_rootAutIsWeylT (hW : RootAutIsWeyl) :
    LangComponentsQuasisimpleT .inner :=
  langComponentsQuasisimple_inner_of_b2T hW b2Two

theorem langComponentsQuasisimple_inner_holdsT :
    LangComponentsQuasisimpleT .inner :=
  langComponentsQuasisimple_inner_of_rootAutIsWeylT
    CFSG.HardMathSupport.Timmesfeld.RootAut.rootAutIsWeyl_holds

end CFSG.HardMathSupport.Timmesfeld.LangTorus
