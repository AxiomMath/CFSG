module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76SigRestrict

public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard03

open CFSG Subgroup CFSG.ComponentClassification.FooteLit

@[expose] def CentralSquareFour (Q : Type) [Group Q] : Prop :=
  ∀ x : Q, x * x ∈ center Q → ∃ A : Subgroup Q, IsKleinFour A ∧ A ≤ centralizer {x}

@[expose] def QuasisimpleCentralSquareFour : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsQuasisimple Q → pPrimeCore 2 Q = ⊥ →
    Blueprint.Catalog (Q ⧸ center Q) → 3 ≤ CFSG.pRank 2 Q →
    (∀ Z : Subgroup Q, Z ≤ center Q → ¬ IsKleinFour Z) → ¬ IsSolomonI Q →
    CentralSquareFour Q

@[expose] def CentralInvolutionJoin : Prop :=
  ∀ (Y : Type) [Group Y] (X : Subgroup Y) (z : Y), orderOf z = 2 → z ∈ X → z ∈ center Y →
    (∀ y : Y, ∃ x ∈ X, x⁻¹ * y ∈ centralizer (X : Set Y)) →
    ¬ IsTwoDisconnected ↥X →
    (∀ x ∈ X, x * x ∈ centralizer (X : Set Y) →
      ∃ A : Subgroup Y, IsKleinFour A ∧ A ≤ X ∧ A ≤ centralizer {x}) →
    ¬ IsTwoDisconnected Y

end CFSG.ComponentClassification.Sol76.Sig.GSYard03
