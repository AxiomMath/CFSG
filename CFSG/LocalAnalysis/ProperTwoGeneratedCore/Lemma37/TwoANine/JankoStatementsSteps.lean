module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoStatementsFrame
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimewiseScalarInvolution
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.BalanceSignalizer

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Subgroup CFSG.Semidihedral.Principal.PrimewiseScalar

namespace JankoFrame

variable {G : Type} [Group G] {z : G} (fr : JankoFrame G z)

@[expose] def M : Subgroup G :=
  oddCoreOf (centralizer (fr.P₁ : Set G))

@[expose] def At : Subgroup G :=
  fr.M ⊓ centralizer ({fr.t} : Set G)

@[expose] def Atz : Subgroup G :=
  fr.M ⊓ centralizer ({fr.t * z} : Set G)

@[expose] def Mbar : Subgroup G :=
  fr.At ⊔ fr.Atz

@[expose] def N : Subgroup G :=
  fr.E ⊔ fr.M

@[expose] def ZN : Subgroup G :=
  fr.N ⊓ centralizer (fr.N : Set G)

@[expose] def P3bar : Subgroup G :=
  fr.ZN ⊓ centralizer ({fr.t} : Set G)

@[expose] def P3bbar : Subgroup G :=
  fr.ZN ⊓ centralizer ({fr.t * z} : Set G)

@[expose] def S : Subgroup G :=
  fr.P3bar ⊔ fr.P3bbar

@[expose] def I : Subgroup G :=
  fr.E ⊔ fr.ZN

@[expose] def U : Subgroup G :=
  oddCoreOf (normalizer (fr.N : Set G))

@[expose] def R (m : G) : Subgroup G :=
  fr.U ⊔ zpowers m

end JankoFrame

variable {G : Type} [Group G] {z : G}

structure JankoProp7 (fr : JankoFrame G z) : Prop where
  isSylowOf_S₁ : IsSylowOf (centralizer (fr.P₁ : Set G)) 2 fr.S₁
  isSylowOf_V : IsSylowOf (centralizer (fr.P₂ : Set G)) 2 fr.V
  isSylowOf_z : IsSylowOf (centralizer (fr.P₃ : Set G)) 2 (zpowers z)
  not_isConj_s₁_s₂ : ¬ IsConj fr.s₁ fr.s₂
  not_isConj_s₁_s₃ : ¬ IsConj fr.s₁ fr.s₃
  not_isConj_s₂_s₃ : ¬ IsConj fr.s₂ fr.s₃
  normalizer_P₁ : normalizer (fr.P₁ : Set G) = centralizer (fr.P₁ : Set G) ⊔ zpowers fr.t
  card_centralizer_P₂_t :
    Nat.card (centralizer (fr.P₂ : Set G) ⊓ centralizer ({fr.t} : Set G) : Subgroup G) = 108
  isConj_of_mem_centralizer : ∀ u : G, orderOf u = 2 → ∀ x ∈ centralizer ({u} : Set G),
    x ^ 3 = 1 → x ≠ 1 → IsConj x fr.s₁ ∨ IsConj x fr.s₂ ∨ IsConj x fr.s₃
  isConj_s₁_iff : ∀ u : G, orderOf u = 2 → ∀ x ∈ centralizer ({u} : Set G), x ^ 3 = 1 →
    (IsConj x fr.s₁ ↔
      Nat.card (centralizer ({x} : Set G) ⊓ centralizer ({u} : Set G) : Subgroup G) = 2160)
  isConj_s₂_iff : ∀ u : G, orderOf u = 2 → ∀ x ∈ centralizer ({u} : Set G), x ^ 3 = 1 →
    (IsConj x fr.s₂ ↔
      Nat.card (centralizer ({x} : Set G) ⊓ centralizer ({u} : Set G) : Subgroup G) = 108)
  isConj_s₃_iff : ∀ u : G, orderOf u = 2 → ∀ x ∈ centralizer ({u} : Set G), x ^ 3 = 1 →
    (IsConj x fr.s₃ ↔
      Nat.card (centralizer ({x} : Set G) ⊓ centralizer ({u} : Set G) : Subgroup G) = 162)
  card_le_two : ∀ y : G, IsConj y fr.s₃ → ∀ B : Subgroup G, B ≤ centralizer ({y} : Set G) →
    IsPGroup 2 B → Nat.card B ≤ 2

structure JankoProp10 (fr : JankoFrame G z) : Prop where
  P₁_le_M : fr.P₁ ≤ fr.M
  centralizer_P₁ : centralizer (fr.P₁ : Set G) = fr.M ⊔ fr.F
  M_inf_F : fr.M ⊓ fr.F = ⊥
  M_inf_centralizer_z : fr.M ⊓ centralizer ({z} : Set G) = fr.P₁
  card_M : Nat.card fr.M = 3 ^ 5
  M_comm : ∀ a ∈ fr.M, ∀ b ∈ fr.M, a * b = b * a
  M_pow_three : ∀ a ∈ fr.M, a ^ 3 = 1
  centralizer_M : centralizer (fr.M : Set G) ⊓ centralizer (fr.P₁ : Set G) = fr.M
  card_At : Nat.card fr.At = 9
  card_Atz : Nat.card fr.Atz = 9
  At_inf_centralizer_z : fr.At ⊓ centralizer ({z} : Set G) = ⊥
  M_eq : fr.M = fr.P₁ ⊔ fr.At ⊔ fr.Atz
  not_At_le : ¬ fr.At ≤ centralizer (fr.P₂ : Set G)
  isConj_of_mem_At : ∀ x ∈ fr.At, x ≠ 1 → IsConj x fr.s₃
  isConj_of_mem_Atz : ∀ x ∈ fr.Atz, x ≠ 1 → IsConj x fr.s₃
  false_of_sylow : ∀ (N₀ : Sylow 3 G) (y : G), IsConj y fr.s₁ →
    (N₀ : Subgroup G) ⊓ centralizer ((N₀ : Subgroup G) : Set G) = zpowers y →
    ∀ Q : Subgroup G, Q ≤ fr.At → Nat.card Q = 3 →
    ∀ X₀ : Subgroup G, IsPGroup 3 X₀ → X₀ ≤ normalizer (fr.P₁ : Set G) →
      X₀ ≤ normalizer (Q : Set G) → fr.t ∈ normalizer (X₀ : Set G) →
      Nat.card X₀ * 3 = Nat.card N₀ → False

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
