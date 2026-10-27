module

public import Certificates.Certificate3920

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaHAut

open CFSG.EvenSmallLie.UnitarySix.YamadaSec3
open CFSG.Monster.B.Co2 (Rep)


theorem basic_check : basicCheck = true := Certificates.certificate3920.1

theorem normL_check : normLCheck = true := Certificates.certificate3920.2.1

theorem outer_check : outerCheck = true := Certificates.certificate3920.2.2.1

theorem normObj_check : normObjCheck = true := Certificates.certificate3920.2.2.2.1

theorem letter_check : letterCheck = true := Certificates.certificate3920.2.2.2.2.1

theorem l1_check : ∀ x ∈ chA4.grp, ∃ a, Rep 693 a x ∧ l1At a = true :=
  Certificates.certificate3920.2.2.2.2.2.1

theorem p4_check : ∀ x ∈ chK1.grp, ∃ a, Rep 693 a x ∧ p4At a = true :=
  Certificates.certificate3920.2.2.2.2.2.2.1

theorem labA4_check : labA4Check = true := Certificates.certificate3920.2.2.2.2.2.2.2

end CFSG.EvenSmallLie.UnitarySix.YamadaHAut
