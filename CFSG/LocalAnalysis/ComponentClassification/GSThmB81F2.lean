module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81F1
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81Fus2
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81P

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

variable {H₁ : h.L81Hyp}

theorem D_comm_P (H₁ : h.L81Hyp) {e w : H} (he : e ∈ h.D) (hw : w ∈ h.P) : e * w = w * e := by
  have hDP : h.D ⊓ h.P = ⊥ := h.toHyp52.D_inf_P_eq_bot H₁.center_J
  have h1 : e * w * e⁻¹ * w⁻¹ ∈ h.D ⊓ h.P := by
    refine mem_inf.mpr ⟨?_, ?_⟩
    · rw [show e * w * e⁻¹ * w⁻¹ = e * (w * e⁻¹ * w⁻¹) by group]
      exact mul_mem he (h.toHyp52.sec8_conj_mem_D ((inf_le_left : h.P ≤ h.S) hw) (inv_mem he))
    · exact mul_mem (h.toHyp52.conj_mem_P' (h.toHyp52.D_le_S he) hw) (inv_mem hw)
  rw [hDP, mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
  exact h1

namespace Data

variable (d : Data H₁)

abbrev R0 : Subgroup H := h.P ⊔ zpowers d.sigma

theorem R0_le_S : d.R0 ≤ h.S := sup_le (inf_le_left : h.P ≤ h.S) (zpowers_le.mpr d.sigma_mem_S)

theorem rho_eq_one_iff {s : H} (hs : s ∈ h.S) :
    Eight.oddBarAction h.J ⟨s, h.toHyp52.S_le_normalizer hs⟩ = 1 ↔ s ∈ h.P := by
  rw [← MonoidHom.mem_ker, Eight.mem_ker_oddBarAction]
  exact ⟨fun h1 => mem_inf.mpr ⟨hs, h1⟩, fun h1 => (mem_inf.mp h1).2⟩

theorem D_comm_tau (F : d.Facts) {e : H} (he : e ∈ h.D) : d.tau * e = e * d.tau :=
  F.tau_comm e ⟨h.toHyp52.sec8_D_le_Q he, H₁.kloc.D_le_M3 he⟩

theorem D_comm_R0 (F : d.Facts) : ∀ e ∈ h.D, ∀ r ∈ d.R0, e * r = r * e := by
  intro e he r hr
  have hle : d.R0 ≤ centralizer ({e} : Set H) := by
    refine sup_le (fun w hw => mem_centralizer_singleton_iff.mpr (H₁.D_comm_P he hw).symm) ?_
    rw [zpowers_le, mem_centralizer_singleton_iff]
    calc d.sigma * e = d.tau * (d.b * e) := by rw [sigma]; group
      _ = d.tau * (e * d.b) := by rw [H₁.D_comm_P he d.b_mem_P]
      _ = (d.tau * e) * d.b := by group
      _ = (e * d.tau) * d.b := by rw [d.D_comm_tau F he]
      _ = e * d.sigma := by rw [sigma]; group
  exact (mem_centralizer_singleton_iff.mp (hle hr)).symm

theorem tau_not_mem_DP (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) (F : d.Facts) :
    d.tau ∉ h.D ⊔ h.P := by
  intro hτ
  obtain ⟨e, he, w, hw, hew⟩ := Eight.exists_mul_of_mem_sup₂
    (fun x hx y hy => H₁.D_comm_P hx hy) hτ
  have heQ : e ∈ h.Q ⊓ h.M3 := ⟨h.toHyp52.sec8_D_le_Q he, H₁.kloc.D_le_M3 he⟩
  have hwQ : w ∈ h.Q ⊓ h.M3 := by
    have := mul_mem (inv_mem heQ) d.tau_mem
    rwa [hew, inv_mul_cancel_left] at this
  have hwT : w ∈ h.T := mem_inf.mpr ⟨hwQ.1, hw⟩
  have hwa : w ∈ zpowers h.a := by
    rcases h.mem_T_cases d.b_ord d.T_eq d.a_comm_b hwT with h1 | h1 | h1 | h1
    · rw [h1]; exact one_mem _
    · rw [h1]; exact mem_zpowers _
    · exact absurd (h1 ▸ hwQ.2) (d.b_not_mem_M3 hCF1 hCF2)
    · exfalso
      apply d.b_not_mem_M3 hCF1 hCF2
      have := mul_mem (inv_mem h.toHyp52.a_mem_M3) (h1 ▸ hwQ.2)
      rwa [inv_mul_cancel_left] at this
  have hτa : d.tau ∈ h.D ⊔ zpowers h.a := by
    rw [hew]
    exact mul_mem_sup he hwa
  have hle : h.Q ⊓ h.M3 ≤ h.D ⊔ zpowers h.a := by
    rw [F.Q1_eq]
    exact sup_le (sup_le le_sup_left (zpowers_le.mpr hτa)) le_sup_right
  have hc : ∀ u ∈ h.D, ∀ v ∈ zpowers h.a, u * v = v * u := by
    intro u hu v hv
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hv
    exact (Commute.zpow_right (h.toHyp52.comm_a (h.toHyp52.D_le_S hu)) k).eq
  have h1 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute h.D (zpowers h.a) hc).1
  rw [Nat.card_zpowers, h.orderOf_a] at h1
  have h2 := card_le_of_le hle
  rw [F.card_Q1] at h2
  have h3 : Nat.card ↥(h.D ⊔ zpowers h.a) ≤ Nat.card h.D * 2 := by
    rw [← h1]
    exact Nat.le_mul_of_pos_right _ Nat.card_pos
  have h4 := F.eight_le
  omega

theorem sigma_mem_normalizer_P : d.sigma ∈ normalizer (h.P : Set H) := by
  rw [mem_normalizer_iff]
  intro w
  constructor
  · intro hw; exact h.toHyp52.conj_mem_P' d.sigma_mem_S hw
  · intro hw
    have := h.toHyp52.conj_mem_P' (inv_mem d.sigma_mem_S) hw
    rwa [show d.sigma⁻¹ * (d.sigma * w * d.sigma⁻¹) * d.sigma⁻¹⁻¹ = w by group] at this

theorem eq_one_or_of_mem_zpowers_of_mul_self {G : Type*} [Group G] {g w : G} (hg : g * g = 1)
    (hw : w ∈ zpowers g) : w = 1 ∨ w = g := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
  rcases Int.even_or_odd k with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · left
    rw [← two_mul, zpow_mul, zpow_two, hg, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_two, hg, one_zpow, one_mul, zpow_one]

theorem mem_R0_cases {r : H} (hr : r ∈ d.R0) : ∃ w ∈ h.P, r = w ∨ r = w * d.sigma := by
  have hr' : r ∈ ((d.R0 : Subgroup H) : Set H) := hr
  rw [coe_mul_of_right_le_normalizer_left h.P (zpowers d.sigma)
    (zpowers_le.mpr d.sigma_mem_normalizer_P)] at hr'
  obtain ⟨w, hw, v, hv, hwv⟩ := hr'
  beta_reduce at hwv
  rcases eq_one_or_of_mem_zpowers_of_mul_self d.sigma_mul_self hv with h1 | h1
  · exact ⟨w, hw, Or.inl (by rw [← hwv, h1, mul_one])⟩
  · exact ⟨w, hw, Or.inr (by rw [← hwv, h1])⟩

end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB
