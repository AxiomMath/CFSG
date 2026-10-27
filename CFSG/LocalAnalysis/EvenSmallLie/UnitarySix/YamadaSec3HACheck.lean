module

public import Certificates.Certificate3607

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.RankThree.Native
open CFSG.Monster.B.Co2 (Rep)

theorem c11a_check : ∀ x ∈ chZ2S.grp, ∃ a, Rep 693 a x ∧ c11aAt a = true :=
  Certificates.certificate3607.1

theorem c6_check : ∀ x ∈ chLam.grp, ∃ a, Rep 693 a x ∧ c6At a = true :=
  Certificates.certificate3607.2.1

theorem c7_check : ∀ x ∈ chLam.grp, ∀ y ∈ chSig.grp, ∃ a b, Rep 693 a x ∧ Rep 693 b y ∧
    c7At a b = true :=
  Certificates.certificate3607.2.2.1

theorem i5Gen_check : i5GenCheck = true := Certificates.certificate3607.2.2.2.2.1

theorem i5_check : ∀ x ∈ chT1.grp, ∃ a, Rep 693 a x ∧ i5At a = true :=
  Certificates.certificate3607.2.2.2.2.2.1

theorem i8Gen_check : i8GenCheck = true := Certificates.certificate3607.2.2.2.2.2.2.1

theorem i8_check : ∀ x ∈ chX1.grp, ∀ y ∈ chX3.grp, ∃ a b, Rep 693 a x ∧ Rep 693 b y ∧
    i8At a b = true :=
  Certificates.certificate3607.2.2.2.2.2.2.2.1

theorem i8bGen_check : i8bGenCheck = true := Certificates.certificate3607.2.2.2.2.2.2.2.2.1

theorem i8b_check : ∀ x ∈ chX3.grp, ∃ a, Rep 693 a x ∧ i8bAt a = true :=
  Certificates.certificate3607.2.2.2.2.2.2.2.2.2.1

theorem nm_check : nmCheck = true := Certificates.certificate3607.2.2.2.2.2.2.2.2.2.2.1

theorem chX3A3_ok : chX3A3.ok = true := Certificates.certificate3607.2.2.2.2.2.2.2.2.2.2.2.1

theorem chX3A3_order : chX3A3.order = 8192 :=
  Certificates.certificate3607.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chSigA3_ok : chSigA3.ok = true :=
  Certificates.certificate3607.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chSigA3_order : chSigA3.order = 24576 :=
  Certificates.certificate3607.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
