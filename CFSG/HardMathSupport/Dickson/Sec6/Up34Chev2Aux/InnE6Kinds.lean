module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcChar2
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcRDE6
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcSuN

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.Up34Exc

open CFSG.Blueprint.Chevalley

section E6Kinds

set_option linter.unusedSectionVars false


theorem char2Hrat_inner_E6 : Char2Hrat Tag.E6 .inner :=
  char2Hrat_inner (Or.inr (Or.inl rfl)) rdSize_E6 rdGlue_E6

theorem char2Hrat_suN_E6 : Char2Hrat Tag.E6 .suN :=
  char2Hrat_suN (Or.inr (Or.inl rfl)) rdSize_E6

end E6Kinds

end CFSG.HardMathSupport.Dickson.Sec6.Up34Exc
