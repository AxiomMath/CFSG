module

public import CFSG.GH74.GLS.Stage4.RestOut

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.Assembly.LowTwoRank

@[expose] def Ch6Bad3 (G : Type) [Group G] : Prop :=
  ∃ z : G, orderOf z = 2 ∧
    ∃ P : Sylow 3 G, (P : Subgroup G) ≤ oPrimeResidualOf 2 (centralizer ({z} : Set G))

@[expose] def Ch6T2Bad9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs], IsTwoCentralG2TypeG2At G Gs 9 9 → Ch6Bad3 G → False

@[expose] def Ch6T2BadGt9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs] (n : ℕ), 3 ≤ n → IsTwoCentralG2TypeG2At G Gs (3 ^ n) (3 ^ n) →
      Ch6Bad3 G → False

@[expose] def Ch6Case9Plus : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs], IsTwoCentralG2TypeG2At G Gs 9 9 → Ch6OutPlus G

@[expose] def Ch6CaseGt9Plus : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs] (n : ℕ), 3 ≤ n → IsTwoCentralG2TypeG2At G Gs (3 ^ n) (3 ^ n) →
      Ch6OutPlus G

theorem ch6OutPlus_of_cases (h9 : Ch6Case9Plus) (hGt9 : Ch6CaseGt9Plus) (hRest : Ch6CaseRestPlus)
    {G : Type} [Group G] [Finite G] (hStd : Std G) (hr : pRank 2 G = 3) {Gs : Type} [Group Gs]
    (hG2 : IsTwoCentralG2TypeG2 G Gs) : Ch6OutPlus G := by
  obtain ⟨q₁, q₂, hAt⟩ := (isTwoCentralG2TypeG2_iff_exists_at G Gs).1 hG2
  by_cases h99 : q₁ = 9 ∧ q₂ = 9
  · obtain ⟨rfl, rfl⟩ := h99
    exact h9 G hStd hr Gs hAt
  · by_cases hn : ∃ n : ℕ, 3 ≤ n ∧ q₁ = 3 ^ n ∧ q₂ = 3 ^ n
    · obtain ⟨n, hn3, rfl, rfl⟩ := hn
      exact hGt9 G hStd hr Gs n hn3 hAt
    · exact hRest G hStd hr Gs q₁ q₂ hAt h99 hn

end CFSG.GH74.GLS.Stage4.Rest
