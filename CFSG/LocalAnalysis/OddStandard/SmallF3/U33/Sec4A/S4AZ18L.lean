module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AZ18K
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AZ18E

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem z18_invol_tQ1 (h : L41GPh17 t L S x₁ x₂ lam rho) {q : G}
    (hq : q ∈ l41Q1 t x₁ x₂ rho) (hinv : (t * q) * (t * q) = 1) :
    ∃ w ∈ l41Q1 t x₁ x₂ rho, w * t * w⁻¹ = t * q := by
  have htM := z18_t_mem_M t x₁ x₂ rho
  have ht2 : t * t = 1 := t_mul_self h.hyp
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hqq : q * q ∈ l41Y t x₁ x₂ rho := h.q1elem q hq
  have hqt' : q * t = t * q⁻¹ := by
    have h1 : t * q * t * q = 1 := by simpa [mul_assoc] using hinv
    calc q * t = t⁻¹ * (t * q * t * q) * q⁻¹ := by group
      _ = t⁻¹ * q⁻¹ := by rw [h1]; group
      _ = t * q⁻¹ := by rw [htinv]
  have hqt : ⁅q, t⁆ ∈ l41Y t x₁ x₂ rho := by
    have e : ⁅q, t⁆ = t * (q * q)⁻¹ * t⁻¹ := by
      rw [commutatorElement_def, hqt']
      group
    rw [e]
    exact z18_conj_Y h.toL41GPh13 htM (Subgroup.inv_mem _ hqq)
  have hqQ : q ∈ l41Q t x₁ x₂ rho := by
    rw [h.q1facts.Q_eq]
    exact Subgroup.mem_sup_left hq
  have hmemWY : q ∈ ((ctxW t x₁ x₂ ⊔ l41Y t x₁ x₂ rho : Subgroup G) : Set G) := by
    rw [← h.qfacts.cent_Qbar_t]
    exact ⟨hqQ, hqt⟩
  have hqF : q ∈ l41F t x₁ x₂ rho :=
    sup_le (m13_W_le_F h.toL41GPh8)
      ((m13_Y_le_R t x₁ x₂ rho).trans le_sup_left) hmemWY
  have hqR : q ∈ l41R t x₁ x₂ rho := by
    rcases m13_mem_F h.toL41GPh8 hqF with hR | ⟨k, hk, hqk⟩
    · exact hR
    · exfalso
      apply h.q1facts.t_not_mem
      have h2 : q * k⁻¹ ∈ l41Q1 t x₁ x₂ rho :=
        Subgroup.mul_mem _ hq (Subgroup.inv_mem _ (h.q1facts.R_le hk))
      rw [hqk, mul_inv_cancel_right] at h2
      exact h2
  have htq : t * q ∈ conjIn (l41Q t x₁ x₂ rho) t := by
    rw [h.qfacts.orbit_t]
    exact ⟨Set.mem_smul_set.mpr ⟨q, hqR, rfl⟩, hinv⟩
  obtain ⟨g, hgQ, hg⟩ := htq
  have hzN : zpowers t ≤ normalizer ((l41Q1 t x₁ x₂ rho : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    exact mem_normalizer_of_conj_mem fun q' hq' => z18_conj_Q1 h.toL41GPh15 htM hq'
  have hg' : g ∈ ((l41Q1 t x₁ x₂ rho ⊔ zpowers t : Subgroup G) : Set G) := by
    rw [← h.q1facts.Q_eq]
    exact hgQ
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hzN] at hg'
  obtain ⟨q', hq', p, hp, rfl⟩ := Set.mem_mul.mp hg'
  refine ⟨q', hq', ?_⟩
  rw [← hg]
  rcases pt_eq_one_or_of_mem_zpowers h.hyp.ord_t hp with h1 | h1
  · rw [h1]
    group
  · rw [h1]
    calc q' * t * q'⁻¹ = q' * (t * t * t⁻¹) * q'⁻¹ := by group
      _ = q' * t * t * (q' * t)⁻¹ := by group

theorem z18_mem_V1_of_comm (h : L41GPh17 t L S x₁ x₂ lam rho) {V₂ : Subgroup G}
    (hV₂ : IsPGroup 2 V₂) (hV₁ : l41V1 t x₁ x₂ rho lam ≤ V₂) {x : G} (hx : x ∈ V₂)
    (hxt : x * t * x⁻¹ * t⁻¹ ∈ l41Q1 t x₁ x₂ rho) : x ∈ l41V1 t x₁ x₂ rho lam := by
  have htM := z18_t_mem_M t x₁ x₂ rho
  have ht2 : t * t = 1 := t_mul_self h.hyp
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hq : t * (x * t * x⁻¹ * t⁻¹) * t⁻¹ ∈ l41Q1 t x₁ x₂ rho :=
    z18_conj_Q1 h.toL41GPh15 htM hxt
  have he : t * (t * (x * t * x⁻¹ * t⁻¹) * t⁻¹) = x * t * x⁻¹ := by
    calc t * (t * (x * t * x⁻¹ * t⁻¹) * t⁻¹)
        = (t * t) * (x * t * x⁻¹) * (t⁻¹ * t⁻¹) := by group
      _ = x * t * x⁻¹ := by rw [ht2, htinv, ht2]; group
  have hinv : (t * (t * (x * t * x⁻¹ * t⁻¹) * t⁻¹)) * (t * (t * (x * t * x⁻¹ * t⁻¹) * t⁻¹)) =
      1 := by
    rw [he]
    calc x * t * x⁻¹ * (x * t * x⁻¹) = x * (t * t) * x⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  obtain ⟨w, hw, hwt⟩ := z18_invol_tQ1 h hq hinv
  rw [he] at hwt
  have hQV : l41Q1 t x₁ x₂ rho ≤ l41V1 t x₁ x₂ rho lam := le_sup_left
  have hwV : w ∈ V₂ := hV₁ (hQV hw)
  have hc : (w⁻¹ * x) * t = t * (w⁻¹ * x) := by
    have : (w⁻¹ * x) * t * (w⁻¹ * x)⁻¹ = t := by
      calc (w⁻¹ * x) * t * (w⁻¹ * x)⁻¹ = w⁻¹ * (x * t * x⁻¹) * w := by group
        _ = w⁻¹ * (w * t * w⁻¹) * w := by rw [hwt]
        _ = t := by group
    exact (mul_inv_eq_iff_eq_mul.mp this)
  have hcV : w⁻¹ * x ∈ l41V1 t x₁ x₂ rho lam :=
    z18_cent_t_le h.toL41GPh15 hV₂ hV₁ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hwV) hx) hc
  have : x = w * (w⁻¹ * x) := by group
  rw [this]
  exact Subgroup.mul_mem _ (hQV hw) hcV

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
