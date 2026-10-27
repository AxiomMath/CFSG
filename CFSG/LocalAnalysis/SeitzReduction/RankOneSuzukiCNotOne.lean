module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiUSylow

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {K : Type*} [Field K] [Fintype K] [CharP K 2]
  {T₁ R₂ : Subgroup G} {t d : G} {a : ℕ} {u v : G → K} {κ : K} {φ : G → K × K × K} {γ c : K}

namespace SzRCoords2

theorem exists_mem_szU_not_mem (h : SzRCoords2 T₁ R₂ t a u v φ γ c)
    (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    {U U₁ : Subgroup G} (hU : SzU T₁ R₂ t d (Fintype.card K) U U₁) :
    ∃ x ∈ U, x ∉ szR T₁ R₂ t := by
  by_contra hcon
  push Not at hcon
  have h1 := Subgroup.card_le_of_le (show U ≤ szR T₁ R₂ t from hcon)
  rw [hU.card, h.card_szR_eq hc ha hK] at h1
  have hq : 2 ≤ Fintype.card K := by
    rw [hK]
    exact Nat.le_self_pow (by omega) 2
  have h2 : Fintype.card K ^ 3 < Fintype.card K ^ 4 := Nat.pow_lt_pow_right hq (by norm_num)
  nlinarith

theorem sq_eq_one_of_not_inverts (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c)
    (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (hγ : γ = 0) {U U₁ : Subgroup G} (hU : SzU T₁ R₂ t d (Fintype.card K) U U₁)
    (hinv : ∃ r ∈ R₂, t * r * t⁻¹ ≠ r⁻¹) : ∀ r ∈ R₂, r ^ 2 = 1 := by
  have htR := mem_szR_right T₁ R₂ t
  obtain ⟨w, hwU, hwR⟩ := h.exists_mem_szU_not_mem hc ha hK hU
  have hwY := hU.le_normalizer hwU
  obtain ⟨hxR, hx3⟩ := h.thd_conj_t ha hK hwY
  have hx1 : (φ (w * t * w⁻¹)).1 ≠ 0 := by
    intro h0
    apply hU.conj_t_not_mem hinv w hwU hwR
    have hz : w * t * w⁻¹ * t⁻¹ ∈ T₁ ⊔ R₂ := by
      refine (h.thd_eq_zero_iff _ (mul_mem hxR (inv_mem htR))).mp ?_
      rw [h.mul _ hxR _ (inv_mem htR), show t⁻¹ = t from hS.t_inv, h.of_t]
      simp [hx3, CharTwo.add_self_eq_zero]
    have hzR₂ : w * t * w⁻¹ * t⁻¹ ∈ R₂ := by
      refine (h.fst_eq_zero_iff hS hc ha hK hz).mp ?_
      rw [h.mul _ hxR _ (inv_mem htR), show t⁻¹ = t from hS.t_inv, h.of_t]
      simp [h0]
    have e : w * t * w⁻¹ = (w * t * w⁻¹ * t⁻¹) * t := by group
    rw [e]
    exact mul_mem (mem_sup_left hzR₂) (mem_sup_right (mem_zpowers t))
  obtain ⟨l, hl⟩ := SzStartField.exists_pow_theta_add_ne_zero ha hK
  set s₀ := (φ (w * t * w⁻¹)).1 with hs₀
  obtain ⟨t₂, ht₂, ht₂u, -⟩ := hc.surj (l * s₀) 0
  have ht₂R := le_szR_left T₁ R₂ t ht₂
  have hcomm2 : v (t₂ * (w * t * w⁻¹) * t₂⁻¹ * (w * t * w⁻¹)⁻¹) ≠ 0 := by
    rw [h.comm _ ht₂R _ hxR, h.of_T₁ _ ht₂, hγ, ht₂u]
    simp only [szCommMap, hx3, zero_mul, add_zero, mul_zero]
    rw [← hs₀]
    have e : l * s₀ * s₀ ^ 2 ^ (a + 1) + (l * s₀) ^ 2 ^ (a + 1) * s₀ =
        s₀ ^ (2 ^ (a + 1) + 1) * (l ^ 2 ^ (a + 1) + l) := by ring
    rw [e]
    exact mul_ne_zero (pow_ne_zero _ hx1) hl
  have hwinv : w⁻¹ ∈ U := inv_mem hwU
  set D := t₂⁻¹ * (w⁻¹ * t₂ * w⁻¹⁻¹) with hD
  have hDR₂ : D ∈ R₂ := hU.conj_sup _ hwinv _ (mem_sup_left ht₂)
  have hDR := le_szR_mid T₁ R₂ t hDR₂
  have hDA : D ∉ szA₁ T₁ := by
    intro hDA
    have hconj : w⁻¹ * t₂ * w⁻¹⁻¹ ∈ T₁ := by
      have e : w⁻¹ * t₂ * w⁻¹⁻¹ = t₂ * D := by rw [hD]; group
      rw [e]
      exact mul_mem ht₂ (szA₁_le T₁ hDA)
    have h1 := hS.t_comm _ hconj
    apply hcomm2
    have h2 : t₂ * (w * t * w⁻¹) = (w * t * w⁻¹) * t₂ := by
      calc t₂ * (w * t * w⁻¹) = w * ((w⁻¹ * t₂ * w⁻¹⁻¹) * t) * w⁻¹ := by group
        _ = w * (t * (w⁻¹ * t₂ * w⁻¹⁻¹)) * w⁻¹ := by rw [h1]
        _ = (w * t * w⁻¹) * t₂ := by group
    rw [h2, mul_inv_cancel_right, mul_inv_cancel, h.v_one]
  have hcommT : ∀ x ∈ T₁, ∀ r ∈ R₂, x * r = r * x := h.commute_of_gamma_eq_zero hγ
  have hD2 : D ^ 2 = 1 := by
    have h1 : (w⁻¹ * t₂ * w⁻¹⁻¹) ^ 2 = t₂ ^ 2 := by
      rw [show (w⁻¹ * t₂ * w⁻¹⁻¹) ^ 2 = w⁻¹ * t₂ ^ 2 * w⁻¹⁻¹ by simp only [_root_.sq]; group]
      exact hU.conj_szA₁ _ hwinv _ (hc.sq_mem_szA₁ ha hK ht₂)
    have e : w⁻¹ * t₂ * w⁻¹⁻¹ = t₂ * D := by rw [hD]; group
    rw [e] at h1
    have h2 : (t₂ * D) ^ 2 = t₂ ^ 2 * D ^ 2 := by
      have hc' := hcommT t₂ ht₂ D hDR₂
      calc (t₂ * D) ^ 2 = t₂ * (D * t₂) * D := by simp only [_root_.sq]; group
        _ = t₂ * (t₂ * D) * D := by rw [hc']
        _ = t₂ ^ 2 * D ^ 2 := by simp only [_root_.sq]; group
    rw [h2] at h1
    calc D ^ 2 = (t₂ ^ 2)⁻¹ * (t₂ ^ 2 * D ^ 2) := by group
      _ = 1 := by rw [h1, inv_mul_cancel]
  have hρD : (φ D).2.1 ≠ 0 := fun h0 => hDA ((h.snd_eq_zero_iff hDR₂).mp h0)
  have hcD : c * (φ D).2.1 = 0 := by
    have h1 := h.sq D hDR
    rw [hD2, h.v_one, h.of_R₂ D hDR₂, hγ] at h1
    simp only [szSqMap, zero_pow (Nat.succ_ne_zero _), zero_mul, zero_add, add_zero] at h1
    rw [h.of_R₂ D hDR₂]
    linear_combination -h1
  have hc0 : c = 0 := (mul_eq_zero.mp hcD).resolve_right hρD
  intro r hr
  have hrR := le_szR_mid T₁ R₂ t hr
  refine h.v_inj _ (h.sq_mem r hrR) ?_
  rw [h.sq r hrR, h.of_R₂ r hr, hγ, hc0]
  simp [szSqMap, zero_pow (Nat.succ_ne_zero _)]

end SzRCoords2

end CFSG.SeitzReduction.RankOne
