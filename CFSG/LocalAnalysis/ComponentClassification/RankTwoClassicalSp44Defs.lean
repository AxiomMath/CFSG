module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalM12

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type} [Group G]

@[expose] def NoThreeCentralizing (A X : Subgroup G) : Prop :=
  ∀ σ : MulAut ↥A, (∃ k : ℕ, σ ^ 3 ^ k = 1) → (∀ x : ↥A, (x : G) ∈ X → σ x = x) → σ = 1

structure Sp44 (A W L : Subgroup G) (y s y₃ : G) : Prop where
  y_mem : y ∈ W
  orderOf_y : orderOf y = 5
  s_mem : s ∈ A
  conj_W : rightConjugate W s = L
  conj_L : rightConjugate L s = W
  W_le : W ≤ centralizer (L : Set G)
  y₃_mem : y₃ ∈ W
  orderOf_y₃ : orderOf y₃ = 3
  noInv₃ : NoInvolutoryCentralizing A (zpowers y₃ ⊔ L)
  standard₃ : standardComponentIsStandard (L.subgroupOf (centralizer (zpowers y₃ : Set G)))
  not_normal₃ : ¬ (L.subgroupOf (centralizer (zpowers y₃ : Set G))).Normal
  noThree : NoThreeCentralizing A (zpowers y ⊔ L)

@[expose] def J2A4Facts : Prop :=
  ∀ (X : Type) [Group X], NativeSporadic.IsSporadic X .J2 → ∀ V Λ : Subgroup X,
    IsPGroup 2 V → 4 ≤ Nat.card V → Nat.card Λ = 60 → ⁅Λ, Λ⁆ = Λ →
    V ≤ centralizer (Λ : Set X) →
    (∀ x ∈ Λ, orderOf x = 5 → ∃ H : Subgroup X,
      H ≤ ⁅centralizer ({x} : Set X), centralizer ({x} : Set X)⁆ ∧ Nat.card H = 60 ∧
        IsSimpleGroup ↥H) ∧
    (∀ z ∈ Λ, orderOf z = 3 → ∀ β : MulAut X, (∃ k : ℕ, β ^ 5 ^ k = 1) → β z = z → β = 1) ∧
    (∃ f ∈ centralizer (Λ : Set X), orderOf f = 3 ∧ f ∈ normalizer (V : Set X) ∧
      f ∉ centralizer (V : Set X))

@[expose] def M12AutThreeFive : Prop :=
  ∀ (X : Type) [Group X], NativeSporadic.IsSporadic X .M12 → ∀ α : MulAut X,
    (∃ k : ℕ, α ^ 3 ^ k = 1) → ∀ h : X, orderOf h = 5 → α h = h → α = 1

@[expose] def Sp44Endgame : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R W L : Subgroup G) (y s y₃ : G),
    Cfg76 A R (zpowers y) L → Sp44 A W L y s y₃ → False

end CFSG.ComponentClassification.RankTwoClassical
