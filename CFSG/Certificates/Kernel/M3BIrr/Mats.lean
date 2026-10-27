module

public import CFSG.Certificates.Kernel.M3BIrr.Defs
public import CFSG.Certificates.Kernel.Common.Chain

public section

#kc_chain CFSG.KD.M3BI "mats.plan.txt" 884 12641014582891685868

namespace CFSG.KD.M3BI

open Timmesfeld.M3B CFSG.HardMathSupport.MathTwE6.M3BIrr CFSG.KC.M3BIrr

@[expose] noncomputable def A0 : Mat := ofFlat matA0
@[expose] noncomputable def B0 : Mat := ofFlat matB0

@[expose] def suppOK (i : Nat) : Bool :=
  (List.finRange 12).all fun r => (List.finRange 12).all fun c => decide (c.val < 3) || mget (matCi i) r c == 0

@[expose] def spinAt (A B : Mat) (i : Nat) (a₀ : F3) : Bool :=
  (List.finRange 3).all fun a₁ => (List.finRange 3).all fun a₂ =>
    (a₀ == 0 && a₁ == 0 && a₂ == 0) || spinFull A B (vmul (vec3 a₀ a₁ a₂) (matBi i))

end CFSG.KD.M3BI

end
