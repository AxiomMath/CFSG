module

public import CFSG.ClassicalGroups.Orthogonal.Eichler
public import CFSG.Open.Defs

public section

namespace CFSG.ClassicalInvolution.Balance.StrongBalance.Orth

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

@[expose] def GeneratedByQuasisimple {F W : Type} [Field F] [AddCommGroup W] [Module F W]
    (Q : QuadraticForm F W) : Prop :=
  ∃ 𝓗 : Set (Subgroup (W ≃ₗ[F] W)),
    (∀ H ∈ 𝓗, H ≤ elementaryGroup Q ∧ CFSG.Open.IsQuasisimple ↥H ∧
      ∀ g ∈ elementaryGroup Q, ∀ h ∈ H, g * h * g⁻¹ ∈ H) ∧
    elementaryGroup Q ≤ ⨆ H ∈ 𝓗, H

end CFSG.ClassicalInvolution.Balance.StrongBalance.Orth
