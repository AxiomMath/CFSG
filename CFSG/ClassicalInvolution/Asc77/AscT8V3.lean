module

public import CFSG.ClassicalInvolution.Asc77.AscP1SevenDihedral
public import CFSG.ClassicalInvolution.Asc77.AscT3Stmt
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement

namespace T8V

variable (p f : ℕ) [Fact p.Prime]

@[expose] def E4SecNoRoot : Prop :=
  p ≠ 2 → 5 ≤ p ^ f → ∀ n : ℕ, CITBelowU p f n →
    ∀ (X : Type) [Group X] [Finite X], Nat.card X < n →
      ∀ Φ : Set (Subgroup X), HypOmegaMod p f Φ → classicalInvolutionOddCore X = ⊥ →
        omegaGen Φ = ⊤ → (∀ K ∈ Φ, ∀ K' ∈ twinSet Φ K, K' = K) → ¬ T3.DStarConnected Φ →
          ∀ A ∈ Φ, ∀ B ∈ omegaNbr Φ A, ∀ x x' : X, IsUniqueInvolution A x →
            IsUniqueInvolution B x' → x * x' ∈ Subgroup.center X →
              (∀ σ : MulAut X, (∀ k ∈ A, σ k * k⁻¹ ∈ oddCoreOf A) →
                (∀ k ∈ B, σ k * k⁻¹ ∈ oddCoreOf B) → σ * σ ≠ MulAut.conj x) ∧
              (∀ e : X, (∀ k ∈ A, ⁅e, k⁆ ∈ oddCoreOf A) → (∀ k ∈ B, ⁅e, k⁆ ∈ oddCoreOf B) →
                e * e ≠ x * x')

end T8V

end CFSG.ClassicalInvolution.Asc77
