module

public import CFSG.GH74.GLS.Stage4.T2Steps

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.Assembly.LowTwoRank

@[expose] def Ch6T2NumGt : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs] (q₁ q₂ : ℕ), IsTwoCentralG2TypeG2At G Gs q₁ q₂ →
      ¬ (q₁ = 9 ∧ q₂ = 9) → (¬ ∃ n : ℕ, 3 ≤ n ∧ q₁ = 3 ^ n ∧ q₂ = 3 ^ n) → q₂ < q₁ → Ch6Num q₁ q₂

theorem ch6T2Num_of_gt (h : Ch6T2NumGt) : Ch6T2Num := by
  intro G _ _ hStd hr Gs _ q₁ q₂ hAt h99 hn
  by_cases hlt : q₂ < q₁
  · exact h G hStd hr Gs q₁ q₂ hAt h99 hn hlt
  · obtain ⟨z, K₁, K₂, F₁, F₂, iF₁, iF₂, hSet⟩ := ch6_setup hr hAt
    have heq : q₁ = q₂ := le_antisymm (not_lt.1 hlt) hSet.le
    have := hSet.finite₂
    have : Fintype F₂ := Fintype.ofFinite F₂
    obtain ⟨p, -, ⟨n, hp, hcard⟩⟩ := FiniteField.card' F₂
    have hq₂ : q₂ = p ^ (n : ℕ) := by rw [← hSet.card₂, Nat.card_eq_fintype_card, hcard]
    have hp2 : p ≠ 2 := by
      rintro rfl
      have := hSet.odd₂
      rw [hq₂] at this
      exact (Nat.not_even_iff_odd.2 this) (Nat.even_pow.2 ⟨even_two, n.pos.ne'⟩)
    exact ⟨p, hp, hp2, ⟨n, by rw [heq, hq₂]⟩, ⟨n, hq₂⟩, Or.inl heq⟩

end CFSG.GH74.GLS.Stage4.Rest
