module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcFam
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcChar2
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcRDE8
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcSuN

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Dickson.Sec6.Up34Exc

namespace Up34Exc

section E8Kinds

set_option linter.unusedSectionVars false


theorem char2Hrat_inner_E8 : Char2Hrat Tag.E8 .inner :=
  char2Hrat_inner (Or.inr (Or.inr (Or.inr rfl))) rdSize_E8 rdGlue_E8

theorem char2Hrat_suN_E8 : Char2Hrat Tag.E8 .suN :=
  char2Hrat_suN (Or.inr (Or.inr (Or.inr rfl))) rdSize_E8

end E8Kinds

end Up34Exc

namespace Up34Chev2

section E8

set_option linter.unusedSectionVars false


theorem up34C2Inn_E8_holds (hD : Char2Hrat Tag.E8 .twoD) (hE : Char2Hrat Tag.E8 .exc) :
    Up34Chev2Inn FamE8 :=
  up34C2Inn_E8_of_kinds char2Hrat_inner_E8 char2Hrat_suN_E8 hD hE

end E8

end Up34Chev2

end CFSG.HardMathSupport.Dickson.Sec6
