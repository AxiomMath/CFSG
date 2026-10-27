module

public import CFSG.ClassicalInvolution.Asc77.AscT8YC2
public import CFSG.ClassicalInvolution.Asc77.AscT8YA3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T8YY

variable {p f : ℕ} [Fact p.Prime]


theorem c26_13_sc_of_facts (hV : LayerFrattiniFact p f) (hP : PureBCase p f) :
    C26_13_sc p f :=
  c26_13_sc_of_caseB p f (w2caseB_of_facts hV hP)

end T8YY

end CFSG.ClassicalInvolution.Asc77
