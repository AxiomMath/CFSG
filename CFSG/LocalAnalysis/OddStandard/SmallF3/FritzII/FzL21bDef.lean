module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzY4Defs
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.OddStandard.SmallF3.FritzII

@[expose] def Fz21bFix : Prop :=
  ∀ (X N : Type) [CommGroup X] [Group N] (φ : N →* MulAut X) (N₀ : Subgroup N) [N₀.Normal]
    (ρ lam : N), Nonempty (X ≃* FzZ244) → Function.Injective φ → Nat.card N₀ = 2 →
    (∀ n ∈ N₀, n ≠ 1 → ∀ x : X, φ n x = x⁻¹) → Nonempty ((N ⧸ N₀) ≃* FzSigma4) →
    orderOf ρ = 3 → orderOf lam = 2 → lam * ρ * lam⁻¹ = ρ⁻¹ → Nonempty (N ≃* FzZ2xSigma4)

end CFSG.OddStandard.SmallF3.FritzII
