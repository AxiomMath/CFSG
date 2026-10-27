module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Struct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem fx_qb_not_mem_centralizer_of_sq {z y : G} {Q₁ Q₂ : Subgroup G} (hQ₁ : Q₁ ≤ L)
    (hQ₂ : Q₂ ≤ L) (hcard : Nat.card ↥(Q₁ ⊔ Q₂) = 32) (hz : centerIn (Q₁ ⊔ Q₂) = zpowers z)
    (hint : (Q₁ ⊔ Q₂) ⊓ centerIn L = ⊥) (hsq : y * y ∈ centralizer (L : Set G)) :
    y * y * z ∉ centralizer (L : Set G) := by
  intro h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardP : Nat.card ↥(Q₁ ⊔ Q₂) = 2 ^ 5 := by rw [hcard]; norm_num
  obtain ⟨k, hkpos, hk⟩ :=
    IsPGroup.card_center_eq_prime_pow (p := 2) (G := ↥(Q₁ ⊔ Q₂)) hcardP (by norm_num)
  have hcenter_card : Nat.card (centerIn (Q₁ ⊔ Q₂)) = 2 ^ k := by
    rw [centerIn, Subgroup.card_map_of_injective (Q₁ ⊔ Q₂).subtype_injective]
    exact hk
  have hz_ne : z ≠ 1 := by
    intro hz1
    have h1 : Nat.card (centerIn (Q₁ ⊔ Q₂)) = 1 := by
      rw [hz, show zpowers z = ⊥ from Subgroup.zpowers_eq_bot.mpr hz1]
      exact Subgroup.card_bot
    rw [hcenter_card] at h1
    have h2 : 1 < 2 ^ k := Nat.one_lt_pow hkpos.ne' (by norm_num)
    omega
  have hzP : z ∈ Q₁ ⊔ Q₂ := by
    have h1 : z ∈ centerIn (Q₁ ⊔ Q₂) := by rw [hz]; exact Subgroup.mem_zpowers z
    exact (sec5_mem_centerIn_iff.mp h1).1
  have hzL : z ∈ L := sup_le hQ₁ hQ₂ hzP
  have hzcent : z ∈ centralizer (L : Set G) := by
    have hmul : (y * y)⁻¹ * (y * y * z) ∈ centralizer (L : Set G) :=
      (centralizer (L : Set G)).mul_mem ((centralizer (L : Set G)).inv_mem hsq) h
    have heq : (y * y)⁻¹ * (y * y * z) = z := by group
    rwa [heq] at hmul
  have hzcenterL : z ∈ centerIn L :=
    sec5_mem_centerIn_iff.mpr
      ⟨hzL, fun w hw => (Subgroup.mem_centralizer_iff.mp hzcent w hw).symm⟩
  have hzbot : z ∈ (Q₁ ⊔ Q₂) ⊓ centerIn L := ⟨hzP, hzcenterL⟩
  rw [hint] at hzbot
  exact hz_ne (Subgroup.mem_bot.mp hzbot)

end CFSG.OddStandard.SmallF3.Omega
