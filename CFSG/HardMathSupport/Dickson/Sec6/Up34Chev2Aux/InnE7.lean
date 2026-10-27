module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcFam
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcChar2
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcRDE7
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcSuN

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Dickson.Sec6.Up34Exc

namespace Up34Exc

section E7Kinds

set_option linter.unusedSectionVars false


theorem char2Hrat_inner_E7 : Char2Hrat Tag.E7 .inner :=
  char2Hrat_inner (Or.inr (Or.inr (Or.inl rfl))) rdSize_E7 rdGlue_E7

theorem char2Hrat_suN_E7 : Char2Hrat Tag.E7 .suN :=
  char2Hrat_suN (Or.inr (Or.inr (Or.inl rfl))) rdSize_E7

end E7Kinds

end Up34Exc

namespace Up34Chev2

section E7

set_option linter.unusedSectionVars false


theorem up34C2Inn_E7_holds (hD : Char2Hrat Tag.E7 .twoD) (hE : Char2Hrat Tag.E7 .exc) :
    Up34Chev2Inn FamE7 :=
  up34C2Inn_E7_of_kinds char2Hrat_inner_E7 char2Hrat_suN_E7 hD hE

end E7

end Up34Chev2

end CFSG.HardMathSupport.Dickson.Sec6
