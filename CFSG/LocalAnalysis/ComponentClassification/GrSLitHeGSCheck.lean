module

public import Certificates.Certificate22700
public import Certificates.Certificate22701
public import Certificates.Certificate22702

public section

namespace CFSG.ComponentClassification.GrSLit.HeGS

open CFSG.PSL3Four.Native CFSG.Sporadic.HeldB CFSG.Sporadic.SmallOddCore
  CFSG.Monster.B.Co2.Native CFSG.ComponentClassification.GrSLit.HeldFix

theorem heGS_twoB_check :
    hfCTab (hfRep 12 heGSXWord) = idTab 8330 :=
  Certificates.certificate22700

theorem heGS_layer_check :
    (∀ j < 9, comp 8330 (heInnerC0 j) (heInnerC0 j) = idTab 8330) ∧
      heGSKTab (heGSComm2 heGST0Comm) = heGen 0 ∧
      fixesOK 105 (heGen 0) heOmega0 = true ∧
      fixesOK 105 (heGSKTab (heGSComm2 heGSUComm)) heOmega0 = true ∧
      heGSKTab (heGSComm2 heGSUComm) ≠ idTab 8330 ∧
      heGSKTab (heGSComm2 heGSUComm) ≠ heGen 0 ∧
      comp 8330 heGSVTab heGSVTab = idTab 8330 ∧ heGSVTab ≠ idTab 8330 ∧
      heGSFix heGSVTab = 346 ∧ heGSFix (heGSKTab (heDWords.getD 1 [])) ≠ 346 ∧
      heGSFix (heGSKTab (heGSComm2 heGSUComm ++ heDWords.getD 1 [])) ≠ 346 ∧
      heGSFix (heGSKTab (0 :: (heGSComm2 heGSUComm ++ heDWords.getD 1 []))) ≠ 346 ∧
      comp 8330 (heGSKTab (heDWords.getD 0 [])) heGSVTab ≠
        comp 8330 heGSVTab (heGSKTab (heDWords.getD 0 [])) ∧
      comp 8330 (heGSKTab (heDWords.getD 0 [])) (heGSKTab (heDWords.getD 1 [])) ≠
        comp 8330 (heGSKTab (heDWords.getD 1 [])) (heGSKTab (heDWords.getD 0 [])) ∧
      ∀ l ∈ [2, 3, 4, 5, 6, 7, 8, 9], comp 105 (heGSDRep l) (heGSDRep l) ≠ idTab 105 :=
  Certificates.certificate22701

theorem heGS_gen_check :
    heGSOK 10 heGSProg = true ∧ permChk 8330 heGSGTab = true ∧
      comp 8330 heGSGTab (heGen 0) = comp 8330 heGSVTab heGSGTab ∧
      (heGSRun 8330 heGSInit heGSProg)[133]!.1 = heGen 0 ∧
      (heGSRun 8330 heGSInit heGSProg)[134]!.1 = heGen 1 :=
  Certificates.certificate22702

end CFSG.ComponentClassification.GrSLit.HeGS
