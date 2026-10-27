module

public import CFSG.ClassicalInvolution.ModelFacts.L6CMain
public import CFSG.ClassicalInvolution.ModelFacts.L6CL
public import CFSG.ClassicalInvolution.ModelFacts.L6CU

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.ModelFacts.L6C

open CFSG.ClassicalInvolution.Asc77

variable (p f : ℕ) [Fact p.Prime]

theorem layer6Cen4_proved : C25Y.Layer6Cen4 p f :=
  layer6Cen4_of_models (aut164L4 p) (aut164U4 p)

end CFSG.ClassicalInvolution.ModelFacts.L6C
