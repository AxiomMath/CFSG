module

public import Certificates.Certificate3780

public section

namespace CFSG.EvenSmallLie.OmegaEight.CPrimeModel

open CFSG.EvenSmallLie.OmegaEight.Stage1


theorem sigCheck_plus : sigCheck .plus = true := Certificates.certificate3780.1

theorem sigCheck_minus : sigCheck .minus = true := Certificates.certificate3780.2.1

theorem cosetCheck_ok : cosetCheck = true := Certificates.certificate3780.2.2.1

theorem minusCheck_ok : minusCheck = true := Certificates.certificate3780.2.2.2

theorem sigCheck_ok (ε : Eps) : sigCheck ε = true := by
  cases ε
  · exact sigCheck_plus
  · exact sigCheck_minus

end CFSG.EvenSmallLie.OmegaEight.CPrimeModel
