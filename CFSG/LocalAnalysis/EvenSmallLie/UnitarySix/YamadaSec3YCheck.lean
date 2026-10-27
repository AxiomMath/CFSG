module

public import Certificates.Certificate3602

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.RankThree.Native


theorem a2Orb_check : ∀ x ∈ chA2.grp, ∃ a, CFSG.Monster.B.Co2.Rep 693 a x ∧ a2OrbAt a = true :=
  Certificates.certificate3602.1

theorem a1Orb_check : ∀ x ∈ chA1.grp, ∃ a, CFSG.Monster.B.Co2.Rep 693 a x ∧ a1OrbAt a = true :=
  Certificates.certificate3602.2.1

theorem a3Orb_check : ∀ x ∈ chA3.grp, ∃ a, CFSG.Monster.B.Co2.Rep 693 a x ∧ a3OrbAt a = true :=
  Certificates.certificate3602.2.2.1

theorem sing_check : ∀ x ∈ chA1.grp, ∃ a, CFSG.Monster.B.Co2.Rep 693 a x ∧ singAt a = true :=
  Certificates.certificate3602.2.2.2.1

theorem zCls_check : zClsCheck = true := Certificates.certificate3602.2.2.2.2.1

theorem chA2s0_ok : chA2s0.ok = true := Certificates.certificate3602.2.2.2.2.2.1

theorem chA2s0_order : chA2s0.order = 512 := Certificates.certificate3602.2.2.2.2.2.2.1

theorem chA2s1_ok : chA2s1.ok = true := Certificates.certificate3602.2.2.2.2.2.2.2.1

theorem chA2s1_order : chA2s1.order = 512 := Certificates.certificate3602.2.2.2.2.2.2.2.2.1

theorem chA2s2_ok : chA2s2.ok = true := Certificates.certificate3602.2.2.2.2.2.2.2.2.2.1

theorem chA2s2_order : chA2s2.order = 512 :=
  Certificates.certificate3602.2.2.2.2.2.2.2.2.2.2.1

theorem chA1s0_ok : chA1s0.ok = true := Certificates.certificate3602.2.2.2.2.2.2.2.2.2.2.2.1

theorem chA1s0_order : chA1s0.order = 512 :=
  Certificates.certificate3602.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chA1s1_ok : chA1s1.ok = true :=
  Certificates.certificate3602.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chA1s1_order : chA1s1.order = 512 :=
  Certificates.certificate3602.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chA3s0_ok : chA3s0.ok = true :=
  Certificates.certificate3602.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chA3s0_order : chA3s0.order = 4096 :=
  Certificates.certificate3602.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chA3s1_ok : chA3s1.ok = true :=
  Certificates.certificate3602.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chA3s1_order : chA3s1.order = 4096 :=
  Certificates.certificate3602.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chA3s2_ok : chA3s2.ok = true :=
  Certificates.certificate3602.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chA3s2_order : chA3s2.order = 4096 :=
  Certificates.certificate3602.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chA3s3_ok : chA3s3.ok = true :=
  Certificates.certificate3602.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chA3s3_order : chA3s3.order = 4096 :=
  Certificates.certificate3602.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chA3s4_ok : chA3s4.ok = true :=
  Certificates.certificate3602.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chA3s4_order : chA3s4.order = 4096 :=
  Certificates.certificate3602.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem yKeys_check : yKeysCheck = true :=
  Certificates.certificate3602.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem a1Reps_check : a1RepsCheck = true :=
  Certificates.certificate3602.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem singGen_check : singGenCheck = true :=
  Certificates.certificate3602.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
