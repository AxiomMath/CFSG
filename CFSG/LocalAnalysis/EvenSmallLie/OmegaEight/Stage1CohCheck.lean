module

public import Certificates.Certificate3371

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1


theorem relCheck6_plus : relCheck6 .plus = true := Certificates.certificate3371.1

theorem relCheck6_minus : relCheck6 .minus = true := Certificates.certificate3371.2.1

theorem gamCheck_plus : gamSpans .plus := Certificates.certificate3371.2.2.1

theorem gamCheck_minus : gamSpans .minus := Certificates.certificate3371.2.2.2.1

theorem extCheck_plus : extSpans .plus := Certificates.certificate3371.2.2.2.2.1

theorem extCheck_minus : extSpans .minus := Certificates.certificate3371.2.2.2.2.2

theorem cohChecks (ε : Eps) : relCheck6 ε = true ∧ gamSpans ε ∧ extSpans ε := by
  cases ε
  · exact ⟨relCheck6_plus, gamCheck_plus, extCheck_plus⟩
  · exact ⟨relCheck6_minus, gamCheck_minus, extCheck_minus⟩

end CFSG.EvenSmallLie.OmegaEight.Stage1
