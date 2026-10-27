module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2Glue
public import CFSG.LieType.AlgebraicGroups.RationalInnerInvolution

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups (signMaskTuple)


@[expose] def BurgoyneE2TwistedE7Input : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 2 →
    ∀ (g : adjointGroup .E7 K) (a : Fin Tag.E7.rank → Kˣ),
      orderOf (MulAut.conj g * rootDiagAut .E7 K a) = 2 →
      (∀ m : ℕ, (m = 1 ∨ m = 2 ∨ m = 3) → ∀ ψ : MulAut (adjointGroup .E7 K),
        ψ * (MulAut.conj g * rootDiagAut .E7 K a) * ψ⁻¹ ≠
          rootDiagAut .E7 K (signMaskTuple .E7 K m)) →
      BurgCoreFor (MulAut.conj g * rootDiagAut .E7 K a) ∨
        BurgTorusFor (MulAut.conj g * rootDiagAut .E7 K a)

end CFSG.ComponentClassification.Burgoyne.E2
