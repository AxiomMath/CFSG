module

public import CFSG.LocalAnalysis.GLTheoremA.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

@[expose] def I1132UsedAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ (B : Subgroup G) (x : G) (L : Subgroup G), GLAIsBmax p B → IsEssential p B x →
    GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L →
    ¬ B ≤ Subgroup.normalizer (L : Set G) →
    ∃ A : Subgroup G, GLAIsBmax p A ∧ B ⊓ centModSubgroup p L ≤ A ∧
      A ≤ Subgroup.normalizer (L : Set G) ∧
      (∀ a ∈ A, ∃ u ∈ A ⊓ B, ∃ v ∈ A ⊓ centModSubgroup p L, a = u * v) ∧
      ∃ E : Subgroup G, E ≤ A ⊓ closureIn L B ⊓ centModSubgroup p L ∧ IsElemAbelian p E ∧
        Nat.card E = p ^ 3

variable {G : Type} [Group G] [Finite G]

@[expose] def I1412UsedAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ (X K : Subgroup G) (y : G), CFSG.Open.IsKGroup ↥X → GLAPComponent p X K → y ^ p = 1 →
    y ∈ Subgroup.normalizer (K : Set G) →
    ∀ J : Subgroup G, GLAPComponent p (K ⊓ Subgroup.centralizer ({y} : Set G)) J →
      kLevel p (PSimple p J) ≤ kLevel p (PSimple p K)

@[expose] def LBalanceAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ (X P : Subgroup G), CFSG.Open.IsKGroup ↥X → P ≤ X → IsPGroup p P →
    GLAPLayer p (X ⊓ Subgroup.centralizer (P : Set G)) ≤ GLAPLayer p X

end CFSG.LocalAnalysis.GLTheoremA
