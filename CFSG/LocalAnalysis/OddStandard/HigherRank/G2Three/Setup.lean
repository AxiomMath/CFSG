module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.Leaves

public section

namespace CFSG.OddStandard.HigherRank.G2Three

open Subgroup CFSG.Open

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_involution (hS : HRSetting G L) :
    ∃ t : G, t ∈ centralizer (L : Set G) ∧ orderOf t = 2 := by
  have hev : Even (Nat.card ↥(centralizer (L : Set G))) := (hS.std.standard).2.1
  have h2 : 2 ∣ Nat.card ↥(centralizer (L : Set G)) := even_iff_two_dvd.mp hev
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(centralizer (L : Set G))) 2 h2
  exact ⟨(x : G), x.2, by rw [Subgroup.orderOf_coe, hx]⟩

theorem normal_centralizer (hS : HRSetting G L) {t : G} (ht : t ∈ centralizer (L : Set G))
    (ht2 : orderOf t = 2) :
    L ≤ centralizer ({t} : Set G) ∧ (L.subgroupOf (centralizer ({t} : Set G))).Normal ∧
      centralizer ({t} : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨h1, h2, h3, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality
      hS.std.standard ht ht2
  exact ⟨h2, h3, h1⟩

theorem exists_commuting_conjugate (hS : HRSetting G L) {t : G} (ht2 : orderOf t = 2) :
    ∃ x : G, x * t * x⁻¹ ≠ t ∧ t * (x * t * x⁻¹) = (x * t * x⁻¹) * t := by
  by_contra! h
  have htt : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at this
  have ht1 : t ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at ht2
    omega
  haveI : Fintype G := Fintype.ofFinite G
  haveI : IsSimpleGroup G := hS.std.simple
  obtain ⟨N, hNn, hNodd, hN⟩ :=
    CFSG.ZStar.glauberman_zStar G t ht1 htt fun g hg => by
      by_contra hne
      exact h g hne hg.symm
  rcases hNn.eq_bot_or_eq_top with hbot | htop
  · have hcen : t ∈ center G := by
      rw [mem_center_iff]
      intro g
      have h' := hN g
      rw [hbot, mem_bot, mul_inv_eq_one] at h'
      calc g * t = g * t * g⁻¹ * g := by group
        _ = t * g := by rw [h']
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with hc | hc
    · rw [hc, mem_bot] at hcen
      exact ht1 hcen
    · obtain ⟨a, b, hab⟩ := hS.std.nonab
      exact hab ((mem_center_iff.mp (hc ▸ mem_top a : a ∈ center G)) b).symm
  · rw [htop, Subgroup.card_top] at hNodd
    have h2 : 2 ∣ Nat.card G := ht2 ▸ orderOf_dvd_natCard t
    exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr h2)

end Setup

end CFSG.OddStandard.HigherRank.G2Three
