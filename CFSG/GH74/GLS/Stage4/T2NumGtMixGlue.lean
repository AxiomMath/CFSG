module

public import CFSG.GH74.GLS.Stage4.T2NumGtMixPrimeEq
public import CFSG.GH74.GLS.Stage4.T2NumGtTwoPart
public import CFSG.GH74.GLS.Stage4.T2NumGtDefs

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.Assembly.LowTwoRank

theorem ch6Gt_mixed_of_leaves (h1 : Ch6T2Rem) (hA : Ch6MixSecEx)
    (hT : Ch6MixTS) : Ch6GtMixed := by
  intro G _ _ hStd hr Gs _ q₁ q₂ hAt h99 hn hlt hmod
  obtain ⟨z, K₁, K₂, F₁, F₂, iF₁, iF₂, hSet⟩ := ch6_setup hr hAt
  obtain ⟨t, hRem⟩ := h1 G hStd hr Gs q₁ q₂ z K₁ K₂ F₁ F₂ hSet
  obtain ⟨N, u, hz, hK₁, hK₂, hq₁, hq₂, hSec, hCoord⟩ :=
    hA G hr Gs q₁ q₂ z K₁ K₂ F₁ F₂ t hSet hRem hlt hmod
  have := hSet.finite₂
  have : Fintype F₂ := Fintype.ofFinite F₂
  obtain ⟨p, -, ⟨n, hp, hcard⟩⟩ := FiniteField.card' F₂
  have hq₂p : q₂ = p ^ (n : ℕ) := by rw [← hSet.card₂, Nat.card_eq_fintype_card, hcard]
  have hp2 : p ≠ 2 := by
    rintro rfl
    have := hSet.odd₂
    rw [hq₂p] at this
    exact (Nat.not_even_iff_odd.2 this) (Nat.even_pow.2 ⟨even_two, n.pos.ne'⟩)
  obtain ⟨y, R, hTS⟩ := hT G hStd hr Gs q₁ q₂ hAt hlt hmod z K₁ K₂ F₁ F₂ t hSet hRem p n hp hp2 hq₂p N u
    hz hK₁ hK₂ hq₁ hq₂ hCoord hSec
  obtain ⟨m, hm⟩ := ch6Mix_primeEq G Gs q₁ q₂ hlt hmod z K₁ K₂ F₁ F₂ t hSet hRem p n hp hp2 hq₂p N u hz
    hK₁ hK₂ hq₁ hq₂ hCoord hSec y R hTS
  have hm0 : m ≠ 0 := by
    rintro rfl
    have := hSet.five
    simp at hm
    omega
  exact hmod (mixed_not_pow hp hp2 hm hq₂p hm0 n.pos.ne' (t5_two_part_sq hSet))

end CFSG.GH74.GLS.Stage4.Rest
