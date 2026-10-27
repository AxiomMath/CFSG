module

public import Certificates.Certificate3373

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1.Model


theorem autCheck_plus : autCheck .plus = true := Certificates.certificate3373.1

theorem autCheck_minus : autCheck .minus = true := Certificates.certificate3373.2

theorem autChecks (ε : Eps) : autCheck ε = true := by
  cases ε
  · exact autCheck_plus
  · exact autCheck_minus

end CFSG.EvenSmallLie.OmegaEight.Stage1.Model
