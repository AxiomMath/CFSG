module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L115dB

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

theorem sec11d_R_side {T R D Y : Subgroup G} {t z : G} (hDR : D ≤ R)
    (hRD : ∀ g ∈ R, ∀ d ∈ D, g * d * g⁻¹ ∈ D) (hCT : ∀ c ∈ R, c * t = t * c → c ∈ T)
    (hz : ∀ g : G, g * t * g⁻¹ ≠ z) (h : Sec11dCl D Y t z) :
    (∀ g ∈ R, g ∉ T ⊔ D → ∀ k ∈ R, k ∉ T ⊔ D → g⁻¹ * k ∈ T ⊔ D) ∧
      ∀ g ∈ R, g ∉ T ⊔ D → D = zpowers t ⊔ zpowers (g * t * g⁻¹) := by
  have hfacts : ∀ g ∈ R, g ∉ T ⊔ D →
      g * t * g⁻¹ ∈ D ∧ g * t * g⁻¹ ∉ Y ∧ ∀ d ∈ D, g * t * g⁻¹ ≠ d * t * d⁻¹ := by
    intro g hg hgT
    have hu : g * t * g⁻¹ ∈ D := hRD g hg t h.t_mem
    have hu2 : (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := by
      calc (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
        _ = 1 := by rw [h.t_sq]; group
    have hu1 : g * t * g⁻¹ ≠ 1 := fun e => h.t_ne (by
      calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
        _ = 1 := by rw [e]; group)
    refine ⟨hu, h.not_mem_Y hu2 hu1 (hz g), fun d hd hd' => hgT ?_⟩
    have hdR : d ∈ R := hDR hd
    have hc : (d⁻¹ * g) * t = t * (d⁻¹ * g) := by
      calc (d⁻¹ * g) * t = d⁻¹ * (g * t * g⁻¹) * g := by group
        _ = d⁻¹ * (d * t * d⁻¹) * g := by rw [hd']
        _ = t * (d⁻¹ * g) := by group
    have hcT : d⁻¹ * g ∈ T := hCT _ (R.mul_mem (R.inv_mem hdR) hg) hc
    have e : g = d * (d⁻¹ * g) := by group
    rw [e, sup_comm]
    exact Subgroup.mul_mem_sup hd hcT
  refine ⟨fun g hg hgT k hk hkT => ?_, fun g hg hgT => ?_⟩
  · obtain ⟨hu, huY, hut⟩ := hfacts g hg hgT
    obtain ⟨hv, hvY, hvt⟩ := hfacts k hk hkT
    obtain ⟨d, hd, hdk⟩ := h.conj_of_not_cl hu huY hut hv hvY hvt
    have hdR : d ∈ R := hDR hd
    have hc : ((d * g)⁻¹ * k) * t = t * ((d * g)⁻¹ * k) := by
      calc ((d * g)⁻¹ * k) * t = (d * g)⁻¹ * (k * t * k⁻¹) * k := by group
        _ = (d * g)⁻¹ * (d * (g * t * g⁻¹) * d⁻¹) * k := by rw [hdk]
        _ = t * ((d * g)⁻¹ * k) := by group
    have hcT : (d * g)⁻¹ * k ∈ T :=
      hCT _ (R.mul_mem (R.inv_mem (R.mul_mem hdR hg)) hk) hc
    have hgd : g⁻¹ * d * g ∈ D := by
      have := hRD g⁻¹ (R.inv_mem hg) d hd
      simpa using this
    have e : g⁻¹ * k = (g⁻¹ * d * g) * ((d * g)⁻¹ * k) := by group
    rw [e, sup_comm]
    exact Subgroup.mul_mem_sup hgd hcT
  · obtain ⟨hu, huY, hut⟩ := hfacts g hg hgT
    exact (h.gen_of_not_cl hu huY hut).symm

end CFSG.OddStandard.SmallF3.Omega
