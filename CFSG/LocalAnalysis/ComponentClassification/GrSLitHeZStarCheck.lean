module

public import Certificates.Certificate22704

public section

namespace CFSG.ComponentClassification.GrSLit.HeGS

open CFSG.PSL3Four.Native CFSG.Sporadic.HeldB CFSG.Sporadic.SmallOddCore
  CFSG.Monster.B.Co2.Native CFSG.ComponentClassification.GrSLit.HeldFix
  Certificates.GrSLitHeZStar

theorem heZStar_check :
    comp 8330 heZOuterTab heZOuterTab = idTab 8330 ∧ heZOuterTab ≠ idTab 8330 ∧
      heGSFix heZOuterTab = 346 ∧
      comp 8330 heZD1Tab heZD1Tab = idTab 8330 ∧ comp 8330 heZD2Tab heZD2Tab = idTab 8330 ∧
      heZD1Tab ≠ idTab 8330 ∧ heZD2Tab ≠ idTab 8330 ∧ heZD1Tab ≠ heZD2Tab ∧
      comp 8330 heZD1Tab heZD2Tab = comp 8330 heZD2Tab heZD1Tab ∧
      heZSylowOK = true ∧ heZTransOK = true ∧ heZFixOK = true ∧
      heGSFix heZUTab = 346 ∧ heGSFix heZT0UTab = 346 ∧
      comp 8330 heZT0UTab heZT0UTab = idTab 8330 ∧ heZT0UTab ≠ idTab 8330 :=
  Certificates.certificate22704

end CFSG.ComponentClassification.GrSLit.HeGS
