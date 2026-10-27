module

public import Certificates.Certificate3493

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Stage1


theorem relCheck4_plus : relCheck4 .plus = true := Certificates.certificate3493.1

theorem relCheck4_minus : relCheck4 .minus = true := Certificates.certificate3493.2.1

theorem kCheck_spec : kCheck = true := Certificates.certificate3493.2.2.1

theorem sqCheck_spec : sqCheck = true := Certificates.certificate3493.2.2.2.1

theorem centerCheck_plus : centerCheck .plus = true :=
  Certificates.certificate3493.2.2.2.2.1

theorem centerCheck_minus : centerCheck .minus = true :=
  Certificates.certificate3493.2.2.2.2.2

theorem relCheck4_spec (ε : Eps) : relCheck4 ε = true := by
  cases ε
  · exact relCheck4_plus
  · exact relCheck4_minus

theorem centerCheck_spec (ε : Eps) : centerCheck ε = true := by
  cases ε
  · exact centerCheck_plus
  · exact centerCheck_minus

end CFSG.EvenSmallLie.OmegaEight.Chain
