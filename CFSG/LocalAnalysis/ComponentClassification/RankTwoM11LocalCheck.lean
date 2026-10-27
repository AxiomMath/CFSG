module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6Out

public section

namespace CFSG.ComponentClassification.RankTwoM11

open Equiv CFSG.QuasithinUnique.Unc25G2

@[expose] def m11Products : List (Perm (Fin 11)) :=
  (wordPermsT CFSG.Sporadic.Bridge.M11.witnesses0).flatMap fun t₀ =>
    (wordPermsT CFSG.Sporadic.Bridge.M11.witnesses1).flatMap fun t₁ =>
      (wordPermsT CFSG.Sporadic.Bridge.M11.witnesses2).flatMap fun t₂ =>
        (wordPermsT CFSG.Sporadic.Bridge.M11.witnesses3).map fun t₃ => t₀ * (t₁ * (t₂ * t₃))

@[expose] def centralizerList : List (Perm (Fin 11)) :=
  m11Products.filter fun x => decide (x * pA = pA * x)

@[expose] def orderFourOK : Bool :=
  centralizerList.all fun s => decide (s * s ≠ 1) || decide (s = 1) || decide (s = pA) ||
    centralizerList.any fun c =>
      decide ((s * (c * s * c⁻¹)) * (s * (c * s * c⁻¹)) ≠ 1) &&
        decide ((s * (c * s * c⁻¹)) * (s * (c * s * c⁻¹)) *
          ((s * (c * s * c⁻¹)) * (s * (c * s * c⁻¹))) = 1)

theorem orderFourOK_true : orderFourOK = true := by
  decide +kernel

@[expose] def centerOK : Bool :=
  centralizerList.all fun z => decide (z * pB ≠ pB * z) || decide (z = 1)

theorem centerOK_true : centerOK = true := by
  decide +kernel

end CFSG.ComponentClassification.RankTwoM11
