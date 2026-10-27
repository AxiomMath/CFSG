module

public import CFSG.ClassicalInvolution.Asc77.AscT3YSw
public import CFSG.ClassicalInvolution.Asc77.AscT3XAssembly

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

variable (p f : ℕ) [Fact p.Prime]


theorem c20_10a_of_noConj (h : Res10aNoConj p f) : C20_10a p f :=
  c20_10a_of_cyc_noconj p f (res10aCyc_proved p f) h


theorem t3CaseII_of_noConj (h : Res10aNoConj p f) : T3CaseII p f :=
  t3CaseII_of_cyc_noconj p f (res10aCyc_proved p f) h

end CFSG.ClassicalInvolution.Asc77.T3CII
