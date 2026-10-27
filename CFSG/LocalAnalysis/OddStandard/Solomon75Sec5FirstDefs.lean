module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5Defs
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5TwoCount

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS CFSG.OddStandard.Solomon75 CFSG.OddStandard.Solomon75.Sec5Two

open scoped commutatorElement

@[expose] def CompInv (X : Type) [Group X] (n : ℕ) (z b : X) : Prop :=
  ∃ A : Subgroup X, Sec5Comp X n (centralizer ({z} : Set X)) A ∧ b ∈ A ∧ orderOf b = 2

@[expose] def zHull (X : Type) [Group X] (n : ℕ) (z : X) : Subgroup X :=
  ⨆ (b : X) (_ : CompInv X n z b), ⁅oddCoreOf (centralizer ({b} : Set X)), zpowers z⁆

@[expose] def OddHull (X : Type) [Group X] (n : ℕ) (z : X) (O : Subgroup X) : Prop :=
  Odd (Nat.card O) ∧ centralizer ({z} : Set X) ≤ normalizer (O : Set X) ∧
    ∀ b : X, CompInv X n z b →
      oddCoreOf (centralizer ({b} : Set X)) ≤ O ⊔ centralizer ({z} : Set X)

@[expose] def W1 {X : Type} [Group X] (A : Subgroup X) : Subgroup X :=
  ⨆ (b : X) (_ : b ∈ A) (_ : orderOf b = 2), oddCoreOf (centralizer ({b} : Set X))

abbrev TwoComps (X : Type) [Group X] (n : ℕ) (z : X) : Prop :=
  ∃ A₁ A₂ : Subgroup X, Sec5Comp X n (centralizer ({z} : Set X)) A₁ ∧
    Sec5Comp X n (centralizer ({z} : Set X)) A₂ ∧ A₁ ≠ A₂

@[expose] def Wgamma {X : Type} [Group X] [Finite X] (A P : Subgroup X) : Subgroup X :=
  ⨆ (c : X) (_ : c ∈ (Open.properTwoGenCoreGamma (P.subgroupOf A) 2).map A.subtype)
    (_ : orderOf c = 2), oddCoreOf (centralizer ({c} : Set X))

end CFSG.OddStandard.Solomon75
