module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicDefs

public section

namespace CFSG.ComponentClassification.RankTwoExceptional

open Subgroup
open CFSG.ComponentClassification.RankTwoSporadic (IsActionHom)

@[expose] def Co1TwoCControl : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X)
    (ψ : normalizer (L : Set X) →* Blueprint.NativeSporadic.Co1),
    IsActionHom L ⊤ ψ → Odd (Nat.card (center ↥L)) →
    Odd (Nat.card (centralizer (L : Set X))) →
    ∀ (z : X) (hz : z ∈ L), orderOf z = 2 →
      ¬ 2 ∣ (centralizer ({ψ ⟨z, le_normalizer hz⟩} : Set Blueprint.NativeSporadic.Co1)).index →
      (∀ g : X, g * z * g⁻¹ ∈ L → g ∈ normalizer (L : Set X)) →
      ∀ (u : X) (hu : u ∈ L), orderOf u = 2 →
        Nat.card (centralizer ({ψ ⟨u, le_normalizer hu⟩} : Set Blueprint.NativeSporadic.Co1)) =
          389283840 →
        centralizer ({u} : Set X) ≤ normalizer (L : Set X)

end CFSG.ComponentClassification.RankTwoExceptional
