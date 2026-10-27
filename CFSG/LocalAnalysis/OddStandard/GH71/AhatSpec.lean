module

public import CFSG.GH74.GLS.IVK.Defs

public section

namespace CFSG.OddStandard.GH71

open Subgroup CFSG CFSG.GH74.GLS

structure AhatFrame (K : Type) [Group K] [Finite K] (S U : Subgroup K) : Prop where
  cover : IsDoubleCoverOfAlt K 11
  sylow : IsPGroup 2 ↥S
  card : Nat.card ↥S = 2 ^ 8
  U_le : U ≤ S
  four : IVK.IsFourSubgroup U
  U_norm : S ≤ normalizer (U : Set K)

@[expose] def SpecB0 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (S U : Subgroup K), AhatFrame K S U → U ≤ ⁅S, S⁆

@[expose] def SpecB1 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (S : Subgroup K), IsDoubleCoverOfAlt K 11 →
    IsPGroup 2 ↥S → Nat.card ↥S = 2 ^ 8 →
    ∃ X : Subgroup K, Nat.card ↥X = 3 ∧ S ≤ normalizer (X : Set K) ∧
      ∀ W : Subgroup K, IsPGroup 3 ↥W → S ≤ normalizer (W : Set K) → W ≤ X

@[expose] def SpecB2 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (S U : Subgroup K), AhatFrame K S U →
    ∀ X : Subgroup K, Nat.card ↥X = 3 → S ≤ normalizer (X : Set K) →
      ∀ v ∈ U, v ∉ center K → centralizer ({v} : Set K) ≤ normalizer (X : Set K)

@[expose] def SpecB2' : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (S U : Subgroup K), AhatFrame K S U →
    ∀ X : Subgroup K, Nat.card ↥X = 3 → S ≤ normalizer (X : Set K) →
      ∀ v ∈ U, v ∉ center K → pPrimeCoreOf 2 (centralizer ({v} : Set K)) ≤ X

@[expose] def SpecB3 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (S U : Subgroup K), AhatFrame K S U →
    ∀ X : Subgroup K, Nat.card ↥X = 3 → S ≤ normalizer (X : Set K) →
      ∀ v ∈ U, v ∉ center K → ¬ (S ⊓ centralizer ({v} : Set K) ≤ centralizer (X : Set K))

@[expose] def SpecB4 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (S : Subgroup K), IsDoubleCoverOfAlt K 11 →
    IsPGroup 2 ↥S → Nat.card ↥S = 2 ^ 8 →
    ∀ x : K, orderOf x = 3 → S ≤ normalizer ((zpowers x : Subgroup K) : Set K) →
      ∃ h : K, closure {y : K | y ∈ closure ({x, h * x * h⁻¹} : Set K) ∧ orderOf y = 5} =
          closure ({x, h * x * h⁻¹} : Set K) ∧
        8 ∣ Nat.card ↥(closure ({x, h * x * h⁻¹} : Set K))

@[expose] def SpecB5 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsDoubleCoverOfAlt K 11 →
    ∀ N : Subgroup K, N.Normal → N ≤ center K ∨ N = ⊤

@[expose] def AhatSpecAll : Prop :=
  SpecB0 ∧ SpecB1 ∧ SpecB2 ∧ SpecB2' ∧ SpecB3 ∧ SpecB4 ∧ SpecB5

end CFSG.OddStandard.GH71
