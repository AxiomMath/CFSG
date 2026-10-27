module

public import Certificates.Certificate3491

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Stage1


theorem invCheck_plus : invCheck .plus = true := Certificates.certificate3491.1

theorem invCheck_minus : invCheck .minus = true := Certificates.certificate3491.2

theorem invCheck_spec (ε : Eps) : invCheck ε = true := by
  cases ε
  · exact invCheck_plus
  · exact invCheck_minus

end CFSG.EvenSmallLie.OmegaEight.Chain
