module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSec5Center

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mul_mem_coreActionKernel {K : Subgroup G} {g : G} (hgN : g ∈ normalizer (K : Set G))
    {k₀ : G} (hk₀ : k₀ ∈ K)
    (hβ : ∀ e, betaHat K hgN e = jq K ⟨k₀, hk₀⟩ * e * (jq K ⟨k₀, hk₀⟩)⁻¹) :
    k₀ * g ∈ coreActionKernel K := by
  refine ⟨mul_mem (le_normalizer hk₀) hgN, fun j hj => ?_⟩
  have hc : k₀⁻¹ * j * k₀ ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hk₀) hj) hk₀
  have hmem : j⁻¹ * (k₀ * g)⁻¹ * j * (k₀ * g) ∈ K := by
    have := conj_mem_of_mem_normalizer hgN hc
    rw [show j⁻¹ * (k₀ * g)⁻¹ * j * (k₀ * g) = j⁻¹ * (g⁻¹ * (k₀⁻¹ * j * k₀) * g) by group]
    exact K.mul_mem (K.inv_mem hj) this
  show _ ∈ oddIn K
  rw [mem_oddIn_iff hmem]
  have e1 : (⟨j⁻¹ * (k₀ * g)⁻¹ * j * (k₀ * g), hmem⟩ : K) =
      (⟨j, hj⟩ : K)⁻¹ * conjJ K hgN ⟨k₀⁻¹ * j * k₀, hc⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjJ]
    group
  have e2 : (⟨k₀⁻¹ * j * k₀, hc⟩ : K) = (⟨k₀, hk₀⟩ : K)⁻¹ * ⟨j, hj⟩ * ⟨k₀, hk₀⟩ := rfl
  rw [e1, map_mul, map_inv, ← betaHat_jq, hβ, e2, map_mul, map_mul, map_inv]
  group

theorem sylowCentralizer :
    ∀ (G : Type) [Group G] [Finite G] (K P : Subgroup G) (g : G), ⁅K, K⁆ = K →
      IsL34Type (K ⧸ Open.fusionZStar K) → IsSylowTwoIn P K → g ∈ normalizer (K : Set G) →
      (∀ p ∈ P, g * p = p * g) →
      ∃ k ∈ P, k⁻¹ * g ∈ coreActionKernel K ∧ ∀ p ∈ P, k⁻¹ * p⁻¹ * k * p ∈ zStarIn K := by
  intro G _ _ K P g hK hL hP hgN hgP
  obtain ⟨q, l, hqS, hqsurj, hqker, h3, hl, hls, hT⟩ := exists_sylow_standard hK hL hP
  have hQ : IsQSetting q l := ⟨hqS, hqsurj, hqker, h3, hl, hls⟩
  obtain ⟨r, hrR, hr⟩ := exists_realization q hqS hqsurj (betaHat K hgN) (fun e => by
    rw [hqker]
    exact mulEquiv_mem_center_iff _ e)
  have hrT : ∀ t ∈ T0, r * t = t * r := by
    intro t ht
    obtain ⟨p, hpP, hpK, hpt⟩ := exists_over hQ hT ht
    have h1 := hr (jq K ⟨p, hpK⟩)
    have h2 : conjJ K hgN ⟨p, hpK⟩ = ⟨p, hpK⟩ := Subtype.ext (by
      show g⁻¹ * p * g = p
      rw [mul_assoc, ← hgP p hpP, ← mul_assoc, inv_mul_cancel, one_mul])
    rw [betaHat_jq, h2, hpt] at h1
    calc r * t = r * t * r⁻¹ * r := by group
      _ = t * r := by rw [← h1]
  have hrZ := mem_Z0_of_comm_T0 hrR hrT
  obtain ⟨e₀, he₀, hβ⟩ := eq_conj_of_realization hK hqsurj hqker (T0_le_S hrZ.2) hr
  obtain ⟨k₀, hk₀P, hk₀K, rfl⟩ := (hT e₀).1 (he₀ ▸ hrZ.2)
  refine ⟨k₀⁻¹, P.inv_mem hk₀P, by rw [inv_inv]; exact mul_mem_coreActionKernel hgN hk₀K hβ,
    fun p hp => ?_⟩
  have hk0 : q (jq K ⟨k₀⁻¹, hP.1 (P.inv_mem hk₀P)⟩) ∈ Z0 := by
    rw [show (⟨k₀⁻¹, hP.1 (P.inv_mem hk₀P)⟩ : K) = (⟨k₀, hk₀K⟩ : K)⁻¹ from rfl, map_inv,
      map_inv, he₀]
    exact inv_mem hrZ
  exact (mem_Z0_iff_comm hP hqsurj hqker hT (P.inv_mem hk₀P)).1 hk0 p hp

end CFSG.ComponentClassification.GrSLit.L34Facts
