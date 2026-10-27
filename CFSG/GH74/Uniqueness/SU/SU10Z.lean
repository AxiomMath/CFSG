module

public import CFSG.LocalAnalysis.ZStar
public import CFSG.CharacterTheory.TwoRankLowerBound.Helpers

public section

namespace CFSG.GH74.Uniqueness.SU.SU10

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem exists_commuting_conj_ne (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a) {t : G}
    (ht : orderOf t = 2) :
    ∃ g : G, g * t * g⁻¹ ≠ t ∧ (g * t * g⁻¹) * t = t * (g * t * g⁻¹) := by
  by_contra hcon0
  have hcon : ∀ g : G, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) → g * t * g⁻¹ = t := by
    intro g hg
    by_contra hne
    exact hcon0 ⟨g, hne, hg⟩
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht, sq] at this
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar G t ht1 ht2 hcon
  rcases CFSG.eq_bot_or_eq_top_of_normal N hNn with h0 | h1
  · have hcen : t ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg := hN g
      rw [h0, Subgroup.mem_bot] at hg
      have : g * t * g⁻¹ = t := by
        have h3 : g * t * g⁻¹ * t⁻¹ = 1 := hg
        rwa [mul_inv_eq_one] at h3
      calc g * t = g * t * g⁻¹ * g := by group
        _ = t * g := by rw [this]
    rw [CFSG.TwoRankLowerBound.Helpers.center_eq_bot_of_nonabelian_simple G hn,
      Subgroup.mem_bot] at hcen
    exact ht1 hcen
  · have hcard : Nat.card N = Nat.card G := by rw [h1]; exact Subgroup.card_top
    have hdvd : orderOf t ∣ Nat.card G := orderOf_dvd_natCard t
    rw [ht, ← hcard] at hdvd
    exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr hdvd)

theorem exists_conj_mem_sylow_ne (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a)
    (S : Sylow 2 G) {t : G} (ht : orderOf t = 2) (htS : ∀ s ∈ (S : Subgroup G), s * t = t * s) :
    ∃ g : G, g * t * g⁻¹ ≠ t ∧ g * t * g⁻¹ ∈ (S : Subgroup G) := by
  obtain ⟨g₀, hne, hcomm⟩ := exists_commuting_conj_ne hs hn ht
  have hSC : (S : Subgroup G) ≤ centralizer ({t} : Set G) := by
    intro s hs'
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact htS s hs'
  have hvC : g₀ * t * g₀⁻¹ ∈ centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm
  have hv2' : orderOf (g₀ * t * g₀⁻¹) = 2 := by
    simpa [ht] using (MulAut.conj g₀).orderOf_eq t
  have hv2 : orderOf (⟨g₀ * t * g₀⁻¹, hvC⟩ : centralizer ({t} : Set G)) = 2 :=
    (Subgroup.orderOf_coe (⟨g₀ * t * g₀⁻¹, hvC⟩ : centralizer ({t} : Set G))).symm.trans hv2'
  have hp : IsPGroup 2 (zpowers (⟨g₀ * t * g₀⁻¹, hvC⟩ : centralizer ({t} : Set G))) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hv2]
    simp
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (centralizer ({t} : Set G)) Q (S.subtype hSC)
  have hmem : MulAut.conj c • (⟨g₀ * t * g₀⁻¹, hvC⟩ : centralizer ({t} : Set G)) ∈
      ((c • Q : Sylow 2 (centralizer ({t} : Set G))) : Subgroup (centralizer ({t} : Set G))) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hQ (Subgroup.mem_zpowers _))
  rw [hc, Sylow.coe_subtype, Subgroup.mem_subgroupOf] at hmem
  have hct : (c : G) * t = t * c := Subgroup.mem_centralizer_singleton_iff.mp c.2
  have hmem' : ((c : G) * g₀) * t * ((c : G) * g₀)⁻¹ ∈ (S : Subgroup G) := by
    have : ((c : G) * g₀) * t * ((c : G) * g₀)⁻¹ = (c : G) * (g₀ * t * g₀⁻¹) * (c : G)⁻¹ := by
      group
    rw [this]
    simpa [MulAut.smul_def, mul_assoc] using hmem
  refine ⟨(c : G) * g₀, ?_, hmem'⟩
  intro heq
  apply hne
  have h1 : (c : G) * (g₀ * t * g₀⁻¹) * (c : G)⁻¹ = t := by
    have : ((c : G) * g₀) * t * ((c : G) * g₀)⁻¹ = (c : G) * (g₀ * t * g₀⁻¹) * (c : G)⁻¹ := by
      group
    rw [← this]
    exact heq
  calc g₀ * t * g₀⁻¹ = (c : G)⁻¹ * ((c : G) * (g₀ * t * g₀⁻¹) * (c : G)⁻¹) * c := by group
    _ = (c : G)⁻¹ * t * c := by rw [h1]
    _ = t := by rw [mul_assoc, ← hct, ← mul_assoc, inv_mul_cancel, one_mul]

end CFSG.GH74.Uniqueness.SU.SU10
