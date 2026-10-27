module

public import Mathlib.Algebra.Group.End

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

@[expose] def ModH1Trivial {Q W : Type*} [Group Q] [CommGroup W] (ρ : Q →* MulAut W) : Prop :=
  ∀ f : Q → W, (∀ q₁ q₂, f (q₁ * q₂) = f q₁ * ρ q₁ (f q₂)) → ∃ w, ∀ q, f q = w * (ρ q w)⁻¹

@[expose] def ModEquivAutTrivial {Q W : Type*} [Group Q] [CommGroup W] (ρ : Q →* MulAut W) :
    Prop :=
  ∀ ψ : W ≃* W, (∀ q w, ψ (ρ q w) = ρ q (ψ w)) → ψ = MulEquiv.refl W

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
