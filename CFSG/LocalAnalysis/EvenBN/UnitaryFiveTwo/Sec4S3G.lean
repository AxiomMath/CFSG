module

import all CFSG.Fischer.F4
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S3D

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaD
open scoped commutatorElement Pointwise

section C7

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem X₂_comm_e₂ {x : G} (hx : x ∈ d.X₂) : x * d.e₂ = d.e₂ * x := by
  obtain ⟨ξ, hξ, rfl⟩ := hx
  have h1 : ξ ∈ Ssub ⊓ centralizer ({e₂SU} : Set SU52) := by
    rw [Ssub_inf_centralizer_e₂SU]
    exact mem_sup_left hξ
  have h2 := mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 h1).2
  change d.ι ξ * d.ι e₂SU = d.ι e₂SU * d.ι ξ
  rw [← map_mul, ← map_mul, h2]

theorem mem_X₂_sup_V₂_of_comm_e₂ (h : d.Hyp) {x : G} (hx : x ∈ d.A₁ ⊔ d.V₂)
    (hxe : x * d.e₂ = d.e₂ * x) : x ∈ d.X₂ ⊔ d.V₂ := by
  have hset := coe_mul_of_left_le_normalizer_right d.A₁ d.V₂ h.A₁_le_normalizer_V₂
  obtain ⟨a, ha, v, hv, rfl⟩ : x ∈ (d.A₁ : Set G) * (d.V₂ : Set G) := by
    rw [← hset]
    exact hx
  have hve : v * d.e₂ = d.e₂ * v := h.Y_comm_e₂ (h.V₂_le_Y hv)
  have hae : a * d.e₂ = d.e₂ * a := by
    calc a * d.e₂ = (a * v) * d.e₂ * v⁻¹ := by
          rw [mul_assoc a v d.e₂, hve, ← mul_assoc, mul_assoc a d.e₂ v, ← mul_assoc]
          group
      _ = d.e₂ * (a * v) * v⁻¹ := by rw [hxe]
      _ = d.e₂ * a := by group
  obtain ⟨α, hα, rfl⟩ := ha
  have h1 : α ∈ Ssub ⊓ centralizer ({e₂SU} : Set SU52) := Subgroup.mem_inf.2
    ⟨A₁sub_le_Ssub hα, mem_centralizer_singleton_iff.2 (d.ι_injective (by
      rw [map_mul, map_mul]
      exact hae))⟩
  rw [Ssub_inf_centralizer_e₂SU] at h1
  have hset' := coe_mul_of_left_le_normalizer_right X₂sub Fsub (fun x hx =>
    mem_normalizer_fintype fun f hf => Ssub_conj_mem_Fsub (X₂sub_le_Ssub hx) hf)
  obtain ⟨ξ, hξ, φ, hφ, hξφ⟩ : α ∈ (X₂sub : Set SU52) * (Fsub : Set SU52) := by
    rw [← hset']
    exact h1
  have hφA : φ ∈ A₁sub := by
    have := mul_mem (inv_mem (X₂sub_le_A₁sub hξ)) hα
    rwa [← hξφ, inv_mul_cancel_left] at this
  have hφZ : φ ∈ Z₂sub := by
    rw [← Fsub_inf_A₁sub]
    exact Subgroup.mem_inf.2 ⟨hφ, hφA⟩
  rw [← hξφ, map_mul]
  have hξX : d.ι ξ ∈ d.X₂ := ⟨ξ, hξ, rfl⟩
  have hφV : d.ι φ ∈ d.V₂ := h.Z₂_le_V₂ ⟨φ, hφZ, rfl⟩
  exact mul_mem (mul_mem (mem_sup_left hξX) (mem_sup_right hφV)) (mem_sup_right hv)

theorem D₃_inf_centralizer_e₂ (h : d.Hyp) :
    d.D₃ ⊓ centralizer ({d.e₂} : Set G) = d.X₂ ⊔ d.V₂ := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxD₃, hxC⟩ := Subgroup.mem_inf.1 hx
    have hxe : x * d.e₂ = d.e₂ * x := mem_centralizer_singleton_iff.1 hxC
    have hxD₁ := D₃_le_D₁' hxD₃
    obtain ⟨a, ha, w, hw, hθ⟩ := h.exists_eq_mul_of_mem_AW (h.theta_mem_AW hxD₁)
    obtain ⟨α, hα, rfl⟩ := ha
    have hxi : mat α 1 0 = 0 := by
      have h0 := (h.mem_D₃_iff_xi hxD₁).1 hxD₃
      rwa [← hθ, h.xi_ι_mul hα hw] at h0
    have hfix : d.e₂ * (d.ι α * w) * d.e₂⁻¹ = d.ι α * w := by
      rw [hθ]
      have e1 : d.e₂ * x * d.e₂⁻¹ * d.t * (d.e₂ * x * d.e₂⁻¹)⁻¹ * d.t =
          d.e₂ * (x * d.t * x⁻¹ * d.t) * d.e₂⁻¹ :=
        crossed_conj_of_mem_H (Subgroup.mem_inf.1 h.e₂_mem_NHS).2
      rw [← e1, show d.e₂ * x * d.e₂⁻¹ = x by rw [← hxe, mul_inv_cancel_right]]
    have hα' : e₂SU * α * e₂SU⁻¹ ∈ A₁sub :=
      conj_mem_A₁sub_of_comm_z (comm_of_mem_CzSub e₂SU_mem_CzSub) hα
    have hw' : d.e₂ * w * d.e₂⁻¹ ∈ d.W :=
      (mem_normalizer_iff.1 (h.NHS_le_normalizer_W h.e₂_mem_NHS) w).1 hw
    have e2 : d.ι (e₂SU * α * e₂SU⁻¹) * (d.e₂ * w * d.e₂⁻¹) = d.ι α * w := by
      rw [← hfix]
      simp only [Data.e₂, map_mul, map_inv]
      group
    have hmem : d.ι (α⁻¹ * (e₂SU * α * e₂SU⁻¹)) ∈ d.W := by
      have : d.ι (α⁻¹ * (e₂SU * α * e₂SU⁻¹)) = w * (d.e₂ * w * d.e₂⁻¹)⁻¹ := by
        rw [map_mul, map_inv]
        calc (d.ι α)⁻¹ * d.ι (e₂SU * α * e₂SU⁻¹)
            = (d.ι α)⁻¹ * (d.ι (e₂SU * α * e₂SU⁻¹) * (d.e₂ * w * d.e₂⁻¹) *
                (d.e₂ * w * d.e₂⁻¹)⁻¹) := by group
          _ = (d.ι α)⁻¹ * (d.ι α * w * (d.e₂ * w * d.e₂⁻¹)⁻¹) := by rw [e2]
          _ = w * (d.e₂ * w * d.e₂⁻¹)⁻¹ := by group
      rw [this]
      exact mul_mem hw (inv_mem hw')
    have hZ : α⁻¹ * (e₂SU * α * e₂SU⁻¹) ∈ ZX₄sub := by
      have h1 : d.ι (α⁻¹ * (e₂SU * α * e₂SU⁻¹)) ∈ d.W ⊓ d.H :=
        Subgroup.mem_inf.2 ⟨hmem, h.L_le_H (d.ι_mem _)⟩
      rw [h.sec4_9_W.2.1] at h1
      exact d.ι_mem_pull_iff.1 h1
    have hc := congrFun ((inv_mul_mem_ZX₄sub_iff hα hα').1 hZ) 1
    change mat α 2 0 = mat (e₂SU * α * e₂SU⁻¹) 2 0 at hc
    rw [mat_conj_e₂_two_zero] at hc
    have hm : (1 - F4.ω) * mat α 2 0 = 0 := by linear_combination hc
    have h20 : mat α 2 0 = 0 := by
      rcases mul_eq_zero.1 hm with h1 | h1
      · exact absurd h1 (by decide)
      · exact h1
    have hαZ : α ∈ Z₂sub := mem_Z₂sub_of_mat hα hxi h20
    have hθZ : x * d.t * x⁻¹ * d.t ∈ d.Z₂ ⊔ d.W := by
      rw [← hθ]
      exact mul_mem (mem_sup_left ⟨α, hαZ, rfl⟩) (mem_sup_right hw)
    have hA₁V₂ : x ∈ d.A₁ ⊔ d.V₂ := (h.sec4_13_4.2.2.2.1 x hxD₁).2 hθZ
    exact h.mem_X₂_sup_V₂_of_comm_e₂ hA₁V₂ hxe
  · refine sup_le (fun x hx => Subgroup.mem_inf.2 ⟨?_, mem_centralizer_singleton_iff.2 (X₂_comm_e₂ hx)⟩)
      (fun v hv => Subgroup.mem_inf.2 ⟨h.V₂_le_D₃ hv, mem_centralizer_singleton_iff.2
        (h.Y_comm_e₂ (h.V₂_le_Y hv))⟩)
    exact X₂_le_A₁.trans h.A₁_le_D₃ hx

theorem M_inf_Y (h : d.Hyp) : d.M ⊓ d.Y = d.V₂ := by
  refine le_antisymm (fun x hx => ?_) (le_inf ?_ h.V₂_le_Y)
  · obtain ⟨hxM, hxY⟩ := Subgroup.mem_inf.1 hx
    have : x ∈ d.D₁ ⊓ d.Y := Subgroup.mem_inf.2 ⟨M_le_D₁ hxM, hxY⟩
    rwa [h.D₁_inf_Y] at this
  · exact fun v hv => Subgroup.mem_inf.2 ⟨h.V₂_le_D₁ hv, mem_centralizer_singleton_iff.2
      (h.Y_comm_e₂ (h.V₂_le_Y hv))⟩

theorem M_le_normalizer_D₃ (h : d.Hyp) : d.M ≤ normalizer (d.D₃ : Set G) := fun m hm =>
  mem_normalizer_fintype fun u hu => h.conj_mem_D₃_of_mem_D₁ (M_le_D₁ hm) hu

theorem card_X₂_sup_V₂ (h : d.Hyp) : Nat.card (d.X₂ ⊔ d.V₂ : Subgroup G) = 2 ^ 8 := by
  have hN : d.X₂ ≤ normalizer (d.V₂ : Set G) := fun x hx =>
    h.A₁_le_normalizer_V₂ (X₂_le_A₁ hx)
  have e := card_sup_mul_card_inf_of_le_normalizer d.V₂ d.X₂ hN
  have hinf : d.V₂ ⊓ d.X₂ = ⊥ := by
    rw [eq_bot_iff, ← h.X₂_inf_D₂]
    exact fun x hx => Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).2,
      h.Y_le_D₂ (h.V₂_le_Y (Subgroup.mem_inf.1 hx).1)⟩
  rw [hinf, Subgroup.card_bot, h.card_V₂, card_X₂ (d := d), sup_comm] at e
  omega

theorem card_M (h : d.Hyp) : Nat.card d.M = 2 ^ 10 := by
  have e := card_sup_mul_card_inf_of_le_normalizer d.D₃ d.M h.M_le_normalizer_D₃
  have hsup : d.D₃ ⊔ d.M = d.D₁ := by
    refine le_antisymm (sup_le D₃_le_D₁' M_le_D₁) fun x hx => ?_
    obtain ⟨u, hu, m, hm, rfl⟩ := h.exists_eq_mul_of_mem_D₁ hx
    exact mul_mem (mem_sup_left hu) (mem_sup_right hm)
  have hinf : d.D₃ ⊓ d.M = d.X₂ ⊔ d.V₂ := by
    rw [← h.D₃_inf_centralizer_e₂]
    apply le_antisymm
    · intro x hx
      obtain ⟨hxD, hxM⟩ := Subgroup.mem_inf.1 hx
      exact Subgroup.mem_inf.2 ⟨hxD, (Subgroup.mem_inf.1 hxM).2⟩
    · intro x hx
      obtain ⟨hxD, hxC⟩ := Subgroup.mem_inf.1 hx
      exact Subgroup.mem_inf.2 ⟨hxD, Subgroup.mem_inf.2 ⟨D₃_le_D₁' hxD, hxC⟩⟩
  rw [hsup, hinf, h.card_D₁, h.card_X₂_sup_V₂, h.card_D₃] at e
  omega

end Data.Hyp

end C7

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
