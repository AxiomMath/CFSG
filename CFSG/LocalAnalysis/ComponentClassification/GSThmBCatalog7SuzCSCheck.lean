module

public import Certificates.Certificate23000
public import Certificates.Certificate23001

public section

namespace CFSG.ComponentClassification.CatFactsL4U4.SuzCS

theorem suzCS_zero_check :
    betaOK = true ∧ outerOK = true ∧ pinOK = true :=
  Certificates.certificate23000

theorem suzCS_three_check : primOK = true :=
  Certificates.certificate23001

end CFSG.ComponentClassification.CatFactsL4U4.SuzCS
