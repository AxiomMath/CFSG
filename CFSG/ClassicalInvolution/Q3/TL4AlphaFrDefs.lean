module

public import CFSG.ClassicalInvolution.Q3.TL4ConnDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)

@[expose] def TightSecLinkGenR (r n : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nat.card X < n → ∀ Φ : Set (Subgroup X), TypeRFam r Φ →
    classicalInvolutionOddCore X = ⊥ → omegaGen Φ = ⊤ → (∀ L ∈ Φ, AEmpty Φ L) →
      ∀ A ∈ Φ, ∀ B ∈ omegaNbr Φ A, B ∈ CoreAssembly.conjClass A →
        ¬ DConnected (CoreAssembly.conjClass A) → ∀ u v : X, IsUniqueInvolution A u →
          IsUniqueInvolution B v →
            Subgroup.centralizer ({u} : Set X) ⊔ Subgroup.centralizer ({v} : Set X) ⊔
              Subgroup.centralizer ({u * v} : Set X) = ⊤

end CFSG.ClassicalInvolution.Q3.TL4
