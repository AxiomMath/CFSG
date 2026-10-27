module

public import Certificates.Certificate3600

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.RankThree.Native

theorem tabs_check : tabsCheck = true := Certificates.certificate3600.1

theorem chS_ok : chS.ok = true := Certificates.certificate3600.2.1

theorem chS_order : chS.order = 32768 := Certificates.certificate3600.2.2.1

theorem chX1_ok : chX1.ok = true := Certificates.certificate3600.2.2.2.1

theorem chX1_order : chX1.order = 4 := Certificates.certificate3600.2.2.2.2.1

theorem chX2_ok : chX2.ok = true := Certificates.certificate3600.2.2.2.2.2.1

theorem chX2_order : chX2.order = 4 := Certificates.certificate3600.2.2.2.2.2.2.1

theorem chX3_ok : chX3.ok = true := Certificates.certificate3600.2.2.2.2.2.2.2.1

theorem chX3_order : chX3.order = 2 := Certificates.certificate3600.2.2.2.2.2.2.2.2.1

theorem chK1_ok : chK1.ok = true := Certificates.certificate3600.2.2.2.2.2.2.2.2.2.1

theorem chK1_order : chK1.order = 25920 := Certificates.certificate3600.2.2.2.2.2.2.2.2.2.2.1

theorem chK2_ok : chK2.ok = true := Certificates.certificate3600.2.2.2.2.2.2.2.2.2.2.2.1

theorem chK2_order : chK2.order = 20160 :=
  Certificates.certificate3600.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chA1_ok : chA1.ok = true := Certificates.certificate3600.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chA1_order : chA1.order = 512 :=
  Certificates.certificate3600.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chA2_ok : chA2.ok = true :=
  Certificates.certificate3600.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chA2_order : chA2.order = 512 :=
  Certificates.certificate3600.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chK1A1_ok : chK1A1.ok = true :=
  Certificates.certificate3600.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chK1A1_order : chK1A1.order = 13271040 :=
  Certificates.certificate3600.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chK2A2_ok : chK2A2.ok = true :=
  Certificates.certificate3600.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chL_ok : chL.ok = true :=
  Certificates.certificate3600.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chL_order : chL.order = 9196830720 :=
  Certificates.certificate3600.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chB12_ok : chB12.ok = true :=
  Certificates.certificate3600.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chB12_order : chB12.order = 60 :=
  Certificates.certificate3600.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chB23_ok : chB23.ok = true :=
  Certificates.certificate3600.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chB23_order : chB23.order = 60 :=
  Certificates.certificate3600.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chSJ_ok : chSJ.ok = true :=
  Certificates.certificate3600.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chSJ_order : chSJ.order = 98304 :=
  Certificates.certificate3600.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chT1_ok : chT1.ok = true :=
  Certificates.certificate3600.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chT1_order : chT1.order = 64 :=
  Certificates.certificate3600.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chT2_ok : chT2.ok = true :=
  Certificates.certificate3600.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chT2_order : chT2.order = 64 :=
  Certificates.certificate3600.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    |>.2.2.1

theorem valid_check : validCheck = true :=
  Certificates.certificate3600.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    |>.2.2.2.1

theorem uNorm_check : uNormCheck = true :=
  Certificates.certificate3600.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    |>.2.2.2.2.1

theorem kNorm_check : kNormCheck = true :=
  Certificates.certificate3600.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    |>.2.2.2.2.2.1

theorem sNorm_check : sNormCheck = true :=
  Certificates.certificate3600.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    |>.2.2.2.2.2.2.1

theorem fix_check : fixCheck = true :=
  Certificates.certificate3600.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    |>.2.2.2.2.2.2.2.1

theorem sIntFix_check : sIntFix = true :=
  Certificates.certificate3600.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    |>.2.2.2.2.2.2.2.2.1

theorem labT1_check : labT1Check = true :=
  Certificates.certificate3600.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    |>.2.2.2.2.2.2.2.2.2.1

theorem t1K1_check : t1K1Check = true :=
  Certificates.certificate3600.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    |>.2.2.2.2.2.2.2.2.2.2.1

theorem sInt_check : ∀ x ∈ chS.grp, ∃ a, CFSG.Monster.B.Co2.Rep 693 a x ∧ sIntAt a = true :=
  Certificates.certificate3600.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    |>.2.2.2.2.2.2.2.2.2.2.2.1

theorem t2Int_check : ∀ x ∈ chT2.grp, ∃ a, CFSG.Monster.B.Co2.Rep 693 a x ∧ t2IntAt a = true :=
  Certificates.certificate3600.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    |>.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem t1Int_check : ∀ x ∈ chT1.grp, ∃ a, CFSG.Monster.B.Co2.Rep 693 a x ∧ t1IntAt a = true :=
  Certificates.certificate3600.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    |>.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem ka1_check : ∀ x ∈ chA1.grp, ∃ a, CFSG.Monster.B.Co2.Rep 693 a x ∧ ka1At a = true :=
  Certificates.certificate3600.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    |>.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem ka2_check : ∀ x ∈ chA2.grp, ∃ a, CFSG.Monster.B.Co2.Rep 693 a x ∧ ka2At a = true :=
  Certificates.certificate3600.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    |>.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem norm_check : ∀ x ∈ chK1.grp, ∃ a, CFSG.Monster.B.Co2.Rep 693 a x ∧ normAt a = true :=
  Certificates.certificate3600.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    |>.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
