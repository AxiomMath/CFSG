module

public import Certificates.Certificate3603

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.RankThree.Native


theorem coordNGen_check : coordNGenCheck = true := Certificates.certificate3603.1

theorem coordN_check : ∀ x ∈ chA1.grp, ∃ a, CFSG.Monster.B.Co2.Rep 693 a x ∧ coordNAt a = true :=
  Certificates.certificate3603.2.1

theorem coordWGen_check : coordWGenCheck = true := Certificates.certificate3603.2.2.1

theorem coordW_check : ∀ x ∈ chA4.grp, ∃ a, CFSG.Monster.B.Co2.Rep 693 a x ∧ coordWAt a = true :=
  Certificates.certificate3603.2.2.2.1

theorem coordWPair_check : ∀ x ∈ chA4.grp, ∀ y ∈ chA4.grp, ∃ a b,
    CFSG.Monster.B.Co2.Rep 693 a x ∧ CFSG.Monster.B.Co2.Rep 693 b y ∧ coordWPairAt a b = true :=
  Certificates.certificate3603.2.2.2.2

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
