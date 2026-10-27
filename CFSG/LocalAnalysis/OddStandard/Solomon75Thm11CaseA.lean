module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Thm11Defs

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

@[expose] def IsLComp (X : Type) [Group X] (L : Subgroup X) : Prop :=
  (∃ t : X, orderOf t = 2 ∧ IsPCompIn 2 (centralizer ({t} : Set X)) L) ∧
    ¬ Group.IsSolvable ↥L

@[expose] def lTwist {X : Type} [Group X] (L : Subgroup X) (t : X) : Subgroup X :=
  oPrimeResidualOf 2 ((L ⊓ centralizer ({t} : Set X)) ⊔ oddCoreOf (centralizer ({t} : Set X)))

@[expose] def LPrec (X : Type) [Group X] (K L : Subgroup X) : Prop :=
  K = L ∨ ∃ s t : X, orderOf s = 2 ∧ orderOf t = 2 ∧ s * t = t * s ∧ s ≠ t ∧
    IsPCompIn 2 (centralizer ({s} : Set X)) K ∧ IsPCompIn 2 (centralizer ({t} : Set X)) L ∧
    t ∈ centralizerSection K (pPrimeCoreOf 2 K) ∧ lTwist K t ≤ L

@[expose] def LBelow (X : Type) [Group X] : Subgroup X → Subgroup X → Prop :=
  Relation.ReflTransGen fun K L => IsLComp X K ∧ IsLComp X L ∧ LPrec X K L

@[expose] def IsLStar (X : Type) [Group X] (L : Subgroup X) : Prop :=
  IsLComp X L ∧ ∀ M : Subgroup X, LBelow X L M → LBelow X M L

@[expose] def IsMaxAhatDeg (X : Type) [Group X] (n : ℕ) : Prop :=
  8 ≤ n ∧ (∃ (t : X) (L : Subgroup X), orderOf t = 2 ∧ IsAhatIntr X t L ∧
      IsDoubleCoverOfAlt (L ⧸ pPrimeCore 2 L) n) ∧
    ∀ (m : ℕ) (t : X) (L : Subgroup X), 8 ≤ m → orderOf t = 2 → IsAhatIntr X t L →
      IsDoubleCoverOfAlt (L ⧸ pPrimeCore 2 L) m → m ≤ n

@[expose] def HypA (X : Type) [Group X] : Prop :=
  ∀ n : ℕ, IsMaxAhatDeg X n → ∀ (t : X) (L : Subgroup X), orderOf t = 2 → IsAhatIntr X t L →
    IsDoubleCoverOfAlt (L ⧸ pPrimeCore 2 L) n → IsLStar X L

end CFSG.OddStandard.Solomon75
