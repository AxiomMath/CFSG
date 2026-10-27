module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitAutL34CertInputs

public section

namespace CFSG.ComponentClassification.HSFLit.AutL34

@[expose] def unitCommOK (TR T0 : List ℕ) : Bool :=
  let Q := T0.filter fun a => commC a r4c
  TR.all fun c => !(commC c r4c) || !(isId (psq c)) || memB c T0 || memB (pcomp r4c c) T0 ||
    Nat.ble (Q.filter fun a => commC a c).length 2

end CFSG.ComponentClassification.HSFLit.AutL34
