module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.HData2

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] [Finite G] {t z z₁ : G} {ι : Elem2 6 →* G} {zv : V6}
  {R0 F : Subgroup G}

theorem eq_bot_of_odd_normal_centralizer (hD2 : HData2 G t z z₁ ι zv R0 F) {U : Subgroup G}
    (hU : U ≤ centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G))
    (hn : ∀ c ∈ centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G), ∀ u ∈ U, c * u * c⁻¹ ∈ U)
    (hodd : Odd (Nat.card U)) : U = ⊥ := by
  have hDU : U ⊓ R0 ≤ U := inf_le_left
  have hDR : U ⊓ R0 ≤ R0 := inf_le_right
  have hDvdU : Nat.card (U ⊓ R0 : Subgroup G) ∣ Nat.card U := Subgroup.card_dvd_of_le hDU
  have hDvdR0 : Nat.card (U ⊓ R0 : Subgroup G) ∣ Nat.card R0 := Subgroup.card_dvd_of_le hDR
  have hDvdR : Nat.card (U ⊓ R0 : Subgroup G) ∣ 2 ^ 8 := by rw [← hD2.card_R0]; exact hDvdR0
  have hcop : Nat.Coprime (Nat.card U) (2 ^ 8) :=
    (Nat.coprime_pow_right_iff (n := 8) (by norm_num) (Nat.card U) 2).mpr
      hodd.coprime_two_right
  have hcardD : Nat.card (U ⊓ R0 : Subgroup G) = 1 := Nat.eq_one_of_dvd_coprimes hcop hDvdU hDvdR
  have hDbot : U ⊓ R0 = ⊥ := Subgroup.eq_bot_of_card_eq (U ⊓ R0) hcardD
  rw [Subgroup.eq_bot_iff_forall]
  intro c hc
  have hcC : c ∈ centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G) := hU hc
  have hR0c : c ∈ R0 := by
    refine hD2.R0_faith c hcC ?_
    intro x hx
    have hxC : x ∈ centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G) := hD2.R0_le hx
    have hconjU : x * c⁻¹ * x⁻¹ ∈ U := hn x hxC c⁻¹ (U.inv_mem hc)
    have hcommU : c * x * c⁻¹ * x⁻¹ ∈ U := by
      simpa only [mul_assoc] using U.mul_mem hc hconjU
    have hcommR : c * x * c⁻¹ * x⁻¹ ∈ R0 :=
      R0.mul_mem (hD2.R0_normal c hcC x hx) (R0.inv_mem hx)
    have hcommD : c * x * c⁻¹ * x⁻¹ ∈ U ⊓ R0 := ⟨hcommU, hcommR⟩
    have hcommbot : c * x * c⁻¹ * x⁻¹ ∈ (⊥ : Subgroup G) := by
      rwa [hDbot] at hcommD
    have hone : c * x * c⁻¹ * x⁻¹ = 1 := Subgroup.mem_bot.mp hcommbot
    rw [hone]
    exact Subgroup.one_mem _
  have hcD : c ∈ U ⊓ R0 := ⟨hc, hR0c⟩
  have hcbot : c ∈ (⊥ : Subgroup G) := by rwa [hDbot] at hcD
  exact Subgroup.mem_bot.mp hcbot

end CFSG.EvenSporadicStandard.HNRecog.Harada
