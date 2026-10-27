module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitAutL34CertInputs

public section

namespace CFSG.ComponentClassification.HSFLit.AutL34

@[expose] def unitNormOK (TR T0 : List ℕ) : Bool :=
  let Q := T0.filter fun a => commC a r4c
  Nat.beq Q.length 8 &&
    TR.all fun c => !(commC c r4c) || !(isId (psq c)) || memB c T0 || memB (pcomp r4c c) T0 ||
      Q.any fun a => !(Nat.beq (pcomp (pcomp a c) (pcube a)) c) &&
        !(Nat.beq (pcomp (pcomp a c) (pcube a)) (pcomp r4c c))

end CFSG.ComponentClassification.HSFLit.AutL34
