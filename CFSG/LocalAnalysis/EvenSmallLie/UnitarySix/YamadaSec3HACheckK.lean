module

public import Certificates.Certificate3606

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.RankThree.Native


theorem c10_check : ∀ x ∈ chK1.grp, ∃ a, CFSG.Monster.B.Co2.Rep 693 a x ∧ c10At a = true :=
  Certificates.certificate3606.1

theorem c8_check : ∀ x ∈ chK1.grp, ∃ a, CFSG.Monster.B.Co2.Rep 693 a x ∧ c8At a = true :=
  Certificates.certificate3606.2.1

theorem c11b_check : ∀ x ∈ chK1.grp, ∃ a, CFSG.Monster.B.Co2.Rep 693 a x ∧ c11bAt a = true :=
  Certificates.certificate3606.2.2.1

theorem labA1_check : labA1Check = true := Certificates.certificate3606.2.2.2.1

theorem z2sKey_check : ∀ x ∈ chZ2S.grp, ∃ a, CFSG.Monster.B.Co2.Rep 693 a x ∧ z2sKeyAt a = true :=
  Certificates.certificate3606.2.2.2.2

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
