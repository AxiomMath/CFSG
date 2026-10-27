module

public import CFSG.Blueprint.Catalog
public import CFSG.Foundations.Basic

public section

namespace CFSG.ComponentClassification.CatFC.DS81

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def DS81OddLie : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    OddLieType X → ∀ τ : X, orderOf τ = 2 →
      CFSG.IsCharacteristicP 2 ↥(centralizer ({τ} : Set X)) →
      IsMulCommutative (CFSG.pCore 2 ↥(centralizer ({τ} : Set X))) →
      ¬ Nonempty (↥(centralizer ({τ} : Set X)) ⧸ CFSG.pCore 2 ↥(centralizer ({τ} : Set X)) ≃*
        Carrier .Co2)

@[expose] def DS81EvenLie : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    EvenLieType X → ∀ τ : X, orderOf τ = 2 →
      CFSG.IsCharacteristicP 2 ↥(centralizer ({τ} : Set X)) →
      IsMulCommutative (CFSG.pCore 2 ↥(centralizer ({τ} : Set X))) →
      ¬ Nonempty (↥(centralizer ({τ} : Set X)) ⧸ CFSG.pCore 2 ↥(centralizer ({τ} : Set X)) ≃*
        Carrier .Co2)

end CFSG.ComponentClassification.CatFC.DS81
