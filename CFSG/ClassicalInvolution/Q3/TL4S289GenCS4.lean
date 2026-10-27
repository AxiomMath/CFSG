module

public import CFSG.ClassicalInvolution.Q3.TL4S289GenB
public import CFSG.ClassicalInvolution.Q3.TL4SecIdMu

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77

namespace S289G

@[expose] def SecIdStarGenS4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)), TypeRFam 3 Φ →
    classicalInvolutionOddCore X = ⊥ → omegaGen Φ = ⊤ →
    (∀ L ∈ Φ, ∀ L' ∈ Φ, ∃ g : X, conjSub g L = L') → ¬ Disconnected.DConnected Φ →
    SecIdLieS4 Φ →
    (∀ M ∈ Φ, ∀ N ∈ omegaNbr Φ M, ∀ m n : X, IsUniqueInvolution M m →
      IsUniqueInvolution N n → m * n ∈ Subgroup.center X) →
      ∀ L ∈ Φ, StarFrameGenAll Φ L

end S289G

end CFSG.ClassicalInvolution.Q3.TL4
