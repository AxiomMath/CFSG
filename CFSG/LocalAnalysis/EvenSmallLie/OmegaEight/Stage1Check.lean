module

public import Certificates.Certificate3370

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1


theorem genCheck_plus : genCheck .plus = true := Certificates.certificate3370.1

theorem genCheck_minus : genCheck .minus = true := Certificates.certificate3370.2.1

theorem orbitCheck_plus : orbitCheck .plus = true := Certificates.certificate3370.2.2.1

theorem orbitCheck_minus : orbitCheck .minus = true :=
  Certificates.certificate3370.2.2.2.1

theorem oCheck_plus : oCheck .plus = true := Certificates.certificate3370.2.2.2.2.1

theorem oCheck_minus : oCheck .minus = true := Certificates.certificate3370.2.2.2.2.2.1

theorem dickCheck_plus : dickCheck .plus = true :=
  Certificates.certificate3370.2.2.2.2.2.2.1

theorem dickCheck_minus : dickCheck .minus = true :=
  Certificates.certificate3370.2.2.2.2.2.2.2.1

theorem coneCheck_plus : coneCheck .plus = true :=
  Certificates.certificate3370.2.2.2.2.2.2.2.2.1

theorem coneCheck_minus : coneCheck .minus = true :=
  Certificates.certificate3370.2.2.2.2.2.2.2.2.2

theorem checks (ε : Eps) : genCheck ε = true ∧ orbitCheck ε = true ∧ oCheck ε = true ∧
    dickCheck ε = true ∧ coneCheck ε = true := by
  cases ε
  · exact ⟨genCheck_plus, orbitCheck_plus, oCheck_plus, dickCheck_plus, coneCheck_plus⟩
  · exact ⟨genCheck_minus, orbitCheck_minus, oCheck_minus, dickCheck_minus, coneCheck_minus⟩

end CFSG.EvenSmallLie.OmegaEight.Stage1
