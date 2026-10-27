module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitAutL34CertInputs

public section

namespace CFSG.ComponentClassification.HSFLit.AutL34

@[expose] def sqCenterOK (T0 : List ℕ) : Bool :=
  T0.all fun z => !(inZB T0 z) || T0.any fun d => Nat.beq (psq d) z

end CFSG.ComponentClassification.HSFLit.AutL34
