module

public import CFSG.Blueprint.NativeSporadic
public import CFSG.Open.Defs

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open CFSG.Blueprint.NativeSporadic
open scoped MatrixGroups

@[expose] def egaLayer (X : Type) [Group X] : Subgroup X :=
  ⨆ (K : Subgroup X) (_ : IsComponentOf K ⊤), K

@[expose] def CaseTwo {G : Type} [Group G] (A : Subgroup G) (z : G) : Prop :=
  ∀ B : Subgroup G, B ≤ A → (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
    Nat.card B = 64 → ¬ normalizer ((B ⊔ zpowers z : Subgroup G) : Set G) ≤
      centralizer ({z} : Set G)

end CFSG.EvenSporadicStandard.M24Std
