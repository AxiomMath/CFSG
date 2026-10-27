module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Basic
public import CFSG.GH74.GLS.Classes

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

@[expose] def IsKType (Q : Type) [Group Q] : Prop :=
  IsQuasisimple Q ∧ ((∃ n : ℕ, 8 ≤ n ∧ IsDoubleCoverOfAlt Q n) ∨
    Nonempty (Q ⧸ center Q ≃* Blueprint.NativeSporadic.McL) ∨
    Nonempty (Q ⧸ center Q ≃* Blueprint.NativeSporadic.Ly))

@[expose] def IsKComp {X : Type} [Group X] (L : Subgroup X) : Prop :=
  IsPComponent 2 L ∧ IsKType (L ⧸ pPrimeCore 2 L)

@[expose] def KProd (X : Type) [Group X] : Subgroup X :=
  sSup {L : Subgroup X | IsKComp L}

@[expose] def KProdIn {X : Type} [Group X] (H : Subgroup X) : Subgroup X :=
  (KProd ↥H).map H.subtype

@[expose] def IsAhatIntr (X : Type) [Group X] (t : X) (L : Subgroup X) : Prop :=
  L ≤ centralizer ({t} : Set X) ∧ t ∈ L ∧
    IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set X))) ∧
    ∃ n : ℕ, 8 ≤ n ∧ IsDoubleCoverOfAlt (L ⧸ pPrimeCore 2 L) n

@[expose] def IsMLIntr (X : Type) [Group X] (t : X) (M : Subgroup X) : Prop :=
  M ≤ centralizer ({t} : Set X) ∧
    IsPComponent 2 (M.subgroupOf (centralizer ({t} : Set X))) ∧
    (Nonempty (M ⧸ pPrimeCore 2 M ≃* Blueprint.NativeSporadic.McL) ∨
      Nonempty (M ⧸ pPrimeCore 2 M ≃* Blueprint.NativeSporadic.Ly)) ∧
    ∀ s ∈ M, orderOf s = 2 → ∃ J : Subgroup X, IsAhatIntr X s J ∧
      J ≤ (M ⊓ centralizer ({s} : Set X)) ⊔ oddCoreOf (centralizer ({s} : Set X))

@[expose] def SolomonThm11At (X : Type) [Group X] : Prop :=
  ∀ t : X, orderOf t = 2 → ∀ L : Subgroup X, (IsAhatIntr X t L ∨ IsMLIntr X t L) → L ≤ KProd X

@[expose] def SolomonThm11 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], SolomonThm11At X

end CFSG.OddStandard.Solomon75
