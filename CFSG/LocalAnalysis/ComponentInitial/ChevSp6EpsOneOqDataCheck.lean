module

public import Certificates.Certificate3361

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne

theorem pCheck_false : pCheck false = true :=
  Certificates.certificate3361.1

theorem pCheck_true : pCheck true = true :=
  Certificates.certificate3361.2.1

theorem eaCheck_false : eaCheck false = true :=
  Certificates.certificate3361.2.2.1

theorem eaCheck_true : eaCheck true = true :=
  Certificates.certificate3361.2.2.2.1

theorem boundCheck_false : boundCheck false = true :=
  Certificates.certificate3361.2.2.2.2.1

theorem boundCheck_true : boundCheck true = true :=
  Certificates.certificate3361.2.2.2.2.2

theorem sylowChecks (u : Bool) :
    pCheck u = true ∧ eaCheck u = true ∧ boundCheck u = true := by
  cases u
  exacts [⟨pCheck_false, eaCheck_false, boundCheck_false⟩,
    ⟨pCheck_true, eaCheck_true, boundCheck_true⟩]

end CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne
