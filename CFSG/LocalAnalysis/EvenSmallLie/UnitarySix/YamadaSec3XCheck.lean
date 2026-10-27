module

public import Certificates.Certificate3601

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.RankThree.Native

theorem xId_check : xIdCheck = true := Certificates.certificate3601.1

theorem xComm_check : xCommCheck = true := Certificates.certificate3601.2.1

theorem xWit_check : xWitCheck = true := Certificates.certificate3601.2.2.1

theorem xNorm_check : xNormCheck = true := Certificates.certificate3601.2.2.2.1

theorem xFix_check : xFixCheck = true := Certificates.certificate3601.2.2.2.2.1

theorem chA3_ok : chA3.ok = true := Certificates.certificate3601.2.2.2.2.2.1

theorem chA3_order : chA3.order = 4096 := Certificates.certificate3601.2.2.2.2.2.2.1

theorem chA4_ok : chA4.ok = true := Certificates.certificate3601.2.2.2.2.2.2.2.1

theorem chA4_order : chA4.order = 16 := Certificates.certificate3601.2.2.2.2.2.2.2.2.1

theorem chX8_ok : chX8.ok = true := Certificates.certificate3601.2.2.2.2.2.2.2.2.2.1

theorem chX8_order : chX8.order = 4 := Certificates.certificate3601.2.2.2.2.2.2.2.2.2.2.1

theorem chSig_ok : chSig.ok = true := Certificates.certificate3601.2.2.2.2.2.2.2.2.2.2.2.1

theorem chSig_order : chSig.order = 6 :=
  Certificates.certificate3601.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chLam_ok : chLam.ok = true := Certificates.certificate3601.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chLam_order : chLam.order = 60 :=
  Certificates.certificate3601.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chZ2S_ok : chZ2S.ok = true :=
  Certificates.certificate3601.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chZ2S_order : chZ2S.order = 8 :=
  Certificates.certificate3601.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chX6Z_ok : chX6Z.ok = true :=
  Certificates.certificate3601.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chX6Z_order : chX6Z.order = 32 :=
  Certificates.certificate3601.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chZ_ok : chZ.ok = true :=
  Certificates.certificate3601.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chZ_order : chZ.order = 2 :=
  Certificates.certificate3601.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chX1Z_ok : chX1Z.ok = true :=
  Certificates.certificate3601.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chP2_ok : chP2.ok = true :=
  Certificates.certificate3601.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chP2_order : chP2.order = 1474560 :=
  Certificates.certificate3601.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem a1Gen_check : a1GenCheck = true :=
  Certificates.certificate3601.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem labA3_check : labA3Check = true :=
  Certificates.certificate3601.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem zS_check : ∀ x ∈ chA2.grp, ∃ a, CFSG.Monster.B.Co2.Rep 693 a x ∧ zSAt a = true :=
  Certificates.certificate3601.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem zA3_check : ∀ x ∈ chA3.grp, ∃ a, CFSG.Monster.B.Co2.Rep 693 a x ∧ zA3At a = true :=
  Certificates.certificate3601.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem a1_check : ∀ x ∈ chA1.grp, ∃ a, CFSG.Monster.B.Co2.Rep 693 a x ∧ a1At a = true :=
  Certificates.certificate3601.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem a4_check : ∀ x ∈ chA4.grp, ∃ a, CFSG.Monster.B.Co2.Rep 693 a x ∧ a4At a = true :=
  Certificates.certificate3601.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    |>.1

theorem a4Pair_check : ∀ x ∈ chA4.grp, ∀ y ∈ chX1.grp, ∃ b a, CFSG.Monster.B.Co2.Rep 693 b y ∧
    CFSG.Monster.B.Co2.Rep 693 a x ∧ a4PairAt b a = true :=
  Certificates.certificate3601.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    |>.2.1

theorem z2s_check : ∀ x ∈ chZ2S.grp, ∃ a, CFSG.Monster.B.Co2.Rep 693 a x ∧ z2sAt a = true :=
  Certificates.certificate3601.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    |>.2.2.1

theorem z2sPair_check : ∀ x ∈ chZ2S.grp, ∀ y ∈ chX1.grp, ∃ b a,
    CFSG.Monster.B.Co2.Rep 693 b y ∧ CFSG.Monster.B.Co2.Rep 693 a x ∧ z2sPairAt b a = true :=
  Certificates.certificate3601.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    |>.2.2.2.1

theorem a2_check : ∀ x ∈ chA2.grp, ∃ a, CFSG.Monster.B.Co2.Rep 693 a x ∧ a2At a = true :=
  Certificates.certificate3601.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    |>.2.2.2.2.1

theorem p2_check : ∀ x ∈ chK1.grp, ∃ a, CFSG.Monster.B.Co2.Rep 693 a x ∧ p2At a = true :=
  Certificates.certificate3601.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    |>.2.2.2.2.2.1

theorem uA_check : uACheck = true :=
  Certificates.certificate3601.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    |>.2.2.2.2.2.2

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
