module

public import Certificates.Certificate22705

public section

namespace CFSG.ComponentClassification.GrSLit.HeGS

open CFSG.PSL3Four.Native CFSG.Sporadic.HeldB Certificates.GrSLitHeZStar Certificates.GrSLitHeF3

theorem heF3_check :
    comp 8330 heF3W1Tab heF3W1Tab = idTab 8330 ∧ comp 8330 heF3W2Tab heF3W2Tab = idTab 8330 ∧
      heF3W12Tab = comp 8330 heF3W2Tab heF3W1Tab ∧
      heF3W1Tab ≠ idTab 8330 ∧ heF3W1Tab ≠ heGen 0 ∧ heF3W1Tab ≠ heZUTab ∧
      heF3W1Tab ≠ heZT0UTab ∧
      heF3W2Tab ≠ idTab 8330 ∧ heF3W2Tab ≠ heGen 0 ∧ heF3W2Tab ≠ heZUTab ∧
      heF3W2Tab ≠ heZT0UTab ∧
      heF3W12Tab ≠ idTab 8330 ∧ heF3W12Tab ≠ heGen 0 ∧ heF3W12Tab ≠ heZUTab ∧
      heF3W12Tab ≠ heZT0UTab :=
  Certificates.certificate22705

end CFSG.ComponentClassification.GrSLit.HeGS
