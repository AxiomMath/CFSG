module

public import CFSG.LocalAnalysis.ZStar
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Blueprint.Chevalley

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]


theorem sec4_exists_conj_commuting [Finite G] (hG : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {t : G} (ht : orderOf t = 2) :
    ∃ s : G, (∃ h : G, s = h⁻¹ * t * h) ∧ s ∈ centralizer ({t} : Set G) ∧ s ≠ t := by
  by_contra h
  have ht1 : t ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at ht
    exact absurd ht (by decide)
  have ht2 : t * t = 1 := by
    have h' := pow_orderOf_eq_one t
    rw [ht, pow_two] at h'
    exact h'
  have hiso : ∀ g : G, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) → g * t * g⁻¹ = t := by
    intro g hg
    by_contra hne
    refine h ⟨g * t * g⁻¹, ⟨g⁻¹, by rw [inv_inv]⟩, ?_, hne⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact hg.symm
  letI : Fintype G := Fintype.ofFinite G
  obtain ⟨N, hNn, hNodd, hNc⟩ := CFSG.ZStar.glauberman_zStar G t ht1 ht2 hiso
  haveI : N.Normal := hNn
  rcases hG.eq_bot_or_eq_top_of_normal N with hNbot | hNtop
  · have htcenter : t ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 : g * t * g⁻¹ * t⁻¹ = 1 := by
        have h' := hNc g
        rwa [hNbot, Subgroup.mem_bot] at h'
      calc g * t = (g * t * g⁻¹ * t⁻¹) * (t * g) := by group
        _ = 1 * (t * g) := by rw [h1]
        _ = t * g := one_mul _
    have hzp_norm : (Subgroup.zpowers t).Normal :=
      Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr htcenter)
    haveI : (Subgroup.zpowers t).Normal := hzp_norm
    rcases hG.eq_bot_or_eq_top_of_normal (Subgroup.zpowers t) with hzp | hzp
    · exfalso
      have htbot : t ∈ (⊥ : Subgroup G) := by
        rw [← hzp]
        exact Subgroup.mem_zpowers t
      have ht1' : t = 1 := Subgroup.mem_bot.mp htbot
      rw [ht1', orderOf_one] at ht
      exact absurd ht (by decide)
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have hle : ⊤ ≤ Subgroup.center G := by
        rw [← hzp]
        exact Subgroup.zpowers_le.mpr htcenter
      exact (Subgroup.mem_center_iff.mp (hle (Subgroup.mem_top a)) b).symm
  · have h2dvd : 2 ∣ Nat.card (⊤ : Subgroup G) := by
      have h' := orderOf_dvd_natCard (⟨t, Subgroup.mem_top t⟩ : (⊤ : Subgroup G))
      rwa [Subgroup.orderOf_mk t (Subgroup.mem_top t), ht] at h'
    rw [hNtop] at hNodd
    exact hNodd.not_two_dvd_nat h2dvd

end CFSG.OddStandard.SmallF3.Omega
