module

public import Certificates.Certificate3530

public section

namespace CFSG.EvenSmallLie.OmegaEight.CPrime

open CFSG.EvenSmallLie.OmegaEight.Stage1


theorem reflRowsCheck_plus : reflRowsCheck .plus = true := Certificates.certificate3530.1

theorem reflRowsCheck_minus : reflRowsCheck .minus = true :=
  Certificates.certificate3530.2.1

theorem reflQfCheck_plus : reflQfCheck .plus = true := Certificates.certificate3530.2.2.1

theorem reflQfCheck_minus : reflQfCheck .minus = true :=
  Certificates.certificate3530.2.2.2.1

theorem sigmaCheck_plus : sigmaCheck .plus = true := Certificates.certificate3530.2.2.2.2.1

theorem sigmaCheck_minus : sigmaCheck .minus = true :=
  Certificates.certificate3530.2.2.2.2.2.1

theorem transNCheck_plus : transNCheck .plus = true :=
  Certificates.certificate3530.2.2.2.2.2.2.1

theorem transNCheck_minus : transNCheck .minus = true :=
  Certificates.certificate3530.2.2.2.2.2.2.2.1

theorem sumCheck_plus : sumCheck .plus = true :=
  Certificates.certificate3530.2.2.2.2.2.2.2.2.1

theorem sumCheck_minus : sumCheck .minus = true :=
  Certificates.certificate3530.2.2.2.2.2.2.2.2.2.1

theorem order3Check_eq : order3Check = true :=
  Certificates.certificate3530.2.2.2.2.2.2.2.2.2.2

theorem cprimeChecks (ε : Eps) : reflRowsCheck ε = true ∧ reflQfCheck ε = true ∧
    sigmaCheck ε = true ∧ transNCheck ε = true ∧ sumCheck ε = true := by
  cases ε
  · exact ⟨reflRowsCheck_plus, reflQfCheck_plus, sigmaCheck_plus, transNCheck_plus,
      sumCheck_plus⟩
  · exact ⟨reflRowsCheck_minus, reflQfCheck_minus, sigmaCheck_minus, transNCheck_minus,
      sumCheck_minus⟩

end CFSG.EvenSmallLie.OmegaEight.CPrime
