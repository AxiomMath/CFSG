module

public import Certificates.Certificate3492

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Stage1


theorem s0Check_plus : s0Check .plus = true := Certificates.certificate3492.1

theorem s0Check_minus : s0Check .minus = true := Certificates.certificate3492.2.1

theorem abelCheck_plus : abelCheck .plus = true := Certificates.certificate3492.2.2.1

theorem abelCheck_minus : abelCheck .minus = true := Certificates.certificate3492.2.2.2

theorem s0Check_spec (ε : Eps) : s0Check ε = true := by
  cases ε
  · exact s0Check_plus
  · exact s0Check_minus

theorem abelCheck_spec (ε : Eps) : abelCheck ε = true := by
  cases ε
  · exact abelCheck_plus
  · exact abelCheck_minus

end CFSG.EvenSmallLie.OmegaEight.Chain
