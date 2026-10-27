module

public import Certificates.Certificate3490

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Stage1


theorem endCheck_plus : endSpans .plus := Certificates.certificate3490.1

theorem endCheck_minus : endSpans .minus := Certificates.certificate3490.2.1

theorem modCheck_plus : modSpans .plus := Certificates.certificate3490.2.2.1

theorem modCheck_minus : modSpans .minus := Certificates.certificate3490.2.2.2

theorem endCheck_spec (ε : Eps) : endSpans ε := by
  cases ε
  · exact endCheck_plus
  · exact endCheck_minus

theorem modCheck_spec (ε : Eps) : modSpans ε := by
  cases ε
  · exact modCheck_plus
  · exact modCheck_minus

end CFSG.EvenSmallLie.OmegaEight.Chain
