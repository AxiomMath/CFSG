module

public import CFSG.ClassicalInvolution.Q3.Q3T8E4Gen

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

@[expose] def E4SecNoRoot3 : Prop :=
  ∀ n : ℕ, CITBelowT (.sl2 3 1) n → IH8T 3 1 n →
    ∀ (X : Type) [Group X] [Finite X], Nat.card X < n →
      ∀ Φ : Set (Subgroup X), HypOmegaModU (.sl2 3 1) Φ → classicalInvolutionOddCore X = ⊥ →
        omegaGen Φ = ⊤ → (∀ L ∈ Φ, AEmpty Φ L) → (∀ K ∈ Φ, ∀ K' ∈ twinSet Φ K, K' = K) →
          ¬ T3.DStarConnected Φ →
            ∀ A ∈ Φ, ∀ B ∈ omegaNbr Φ A, ∀ x x' : X, IsUniqueInvolution A x →
              IsUniqueInvolution B x' → x * x' ∈ Subgroup.center X →
                (∀ σ : MulAut X, (∀ k ∈ A, σ k * k⁻¹ ∈ oddCoreOf A) →
                  (∀ k ∈ B, σ k * k⁻¹ ∈ oddCoreOf B) → σ * σ ≠ MulAut.conj x) ∧
                (∀ e : X, (∀ k ∈ A, ⁅e, k⁆ ∈ oddCoreOf A) → (∀ k ∈ B, ⁅e, k⁆ ∈ oddCoreOf B) →
                  e * e ≠ x * x')

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
