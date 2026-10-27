module

import CFSG.LocalAnalysis.ZStar
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.OddStandard.Solomon75

theorem exists_commuting_conj {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {z : G} (hz : orderOf z = 2) :
    ∃ g : G, g⁻¹ * z * g ≠ z ∧ (g⁻¹ * z * g) * z = z * (g⁻¹ * z * g) := by
  by_contra hcon
  push Not at hcon
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz, sq] at this
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    omega
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨N, hNn, hNodd, hNg⟩ := CFSG.ZStar.glauberman_zStar G z hz1 hzz (fun g hc => by
    by_contra hne
    exact hcon g⁻¹ (by simpa using hne) (by simpa using hc))
  have hNbot : N = ⊥ := by
    have := hNn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exact h
    · exfalso
      have h2 : 2 ∣ Nat.card G := hz ▸ orderOf_dvd_natCard z
      rw [h, Subgroup.card_top] at hNodd
      exact (Nat.not_even_iff_odd.2 hNodd) (even_iff_two_dvd.2 h2)
  have hcentral : ∀ g : G, g * z = z * g := fun g => by
    have h1 : g * z * g⁻¹ * z⁻¹ = 1 := by
      have := hNg g
      rwa [hNbot, Subgroup.mem_bot] at this
    calc g * z = (g * z * g⁻¹ * z⁻¹) * z * g := by group
      _ = z * g := by rw [h1]; group
  have hnormal : (Subgroup.zpowers z).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have h1 : g * z ^ k = z ^ k * g := (Commute.zpow_right (hcentral g) k).eq
    have : g * z ^ k * g⁻¹ = z ^ k := by
      rw [h1]
      group
    rw [this]
    exact Subgroup.zpow_mem_zpowers z k
  have := hnormal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers z) with h | h
  · exact hz1 (Subgroup.zpowers_eq_bot.1 h)
  · obtain ⟨a, b, hab⟩ := hnonab
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (h ▸ Subgroup.mem_top a)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (h ▸ Subgroup.mem_top b)
    apply hab
    rw [← hi, ← hj]
    exact (Commute.zpow_zpow_self z i j).eq

end CFSG.OddStandard.Solomon75
