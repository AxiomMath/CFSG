module

public import CFSG.ClassicalInvolution.Asc77.AscR10E20
public import CFSG.ClassicalInvolution.Asc77.AscR10E24

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.ClassicalInvolution



theorem res10aNoConj9_of_cit3 (p f : ℕ) [Fact p.Prime] :
    Q3.CIT3Inductive → p ^ f = 9 → Res10aNoConj p f :=
  res10aNoConj9_of_orth_exc p f ModelFacts.stdDich3Orth ModelFacts.stdDich3Exc

end CFSG.ClassicalInvolution.Asc77.T3CII
