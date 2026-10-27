module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bTypes

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

@[expose] def CFL2Cent : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f → 5 ≤ p ^ f →
    Blueprint.LieModel Y .PSL 2 p f → ∀ D₀ : Subgroup Y,
    (∃ R : Sylow 2 Y, (R : Subgroup Y) = D₀) →
    ∀ σ : MulAut Y, IsOuterDiagonalPSL2 σ → D₀.map σ.toMonoidHom = D₀ →
    ∀ τ ζ : MulAut Y, (∃ k : ℕ, τ ^ 2 ^ k = 1) → (∃ k : ℕ, ζ ^ 2 ^ k = 1) →
      τ * σ = σ * τ → ζ * σ = σ * ζ → (∀ d ∈ D₀, τ d = d) → (∀ d ∈ D₀, ζ d = d) → ζ ≠ 1 →
      τ = 1 ∨ τ = ζ

end CFSG.ComponentClassification.GSThmB
