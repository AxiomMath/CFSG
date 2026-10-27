module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.Child5Y13K
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.Child5Y13W0

public section

namespace CFSG.EvenSmallLie.UnitarySix.Child5

open Subgroup Matrix YamadaPar YamadaD

variable {G : Type} [Group G] [Finite G] {d : YamadaD.Data G}

theorem D₁_nonab (h : Hyp d) (hB : HypB d) (hV : ∀ v ∈ d.V₁, v * v = 1) :
    ∃ x ∈ d.D₁, ∃ y ∈ d.D₁, x * y ≠ y * x := by
  by_contra hcon
  simp only [not_exists, not_and, ne_eq, not_not] at hcon
  have hle : d.D₁ ≤ d.D₁ ⊓ centralizer (d.D₁ : Set G) :=
    fun x hx => mem_inf.mpr ⟨hx, mem_centralizer_iff.mpr fun y hy => hcon y hy x hx⟩
  rw [h.center_D₁ hB hV] at hle
  have := Subgroup.card_le_of_le hle
  rw [h.card_D₁ hB hV, h.card_V₁] at this
  norm_num at this

theorem mem_D₂_of_comm (h : Hyp d) (hB : HypB d) (hC : HypC d) (hV : ∀ v ∈ d.V₁, v * v = 1)
    (hN : d.D₁ ≤ normalizer (d.D₂ : Set G)) {y x : G} (hy : y ∈ d.D₂) (hx : x ∈ d.D₁) :
    y * x * y⁻¹ * x ∈ d.D₂ := by
  have h1 : x * y⁻¹ * x⁻¹ ∈ d.D₂ := (mem_normalizer_iff.mp (hN hx) _).mp (inv_mem hy)
  have h2 : x * x ∈ d.D₂ := h.V₁_le_D₂ (h.D₁_sq_mod hB hC hV hx)
  have e : y * x * y⁻¹ * x = y * (x * y⁻¹ * x⁻¹) * (x * x) := by group
  rw [e]
  exact mul_mem (mul_mem hy h1) h2

theorem exists_ι_range (h : Hyp d) (hB : HypB d) (hC : HypC d) (hV : ∀ v ∈ d.V₁, v * v = 1)
    {a : G} (ha : a ∈ d.A₁) : ∃ x ∈ d.D₁, (d.t * x * d.t⁻¹ * x)⁻¹ * a ∈ d.V₁ := by
  obtain ⟨y, hy, hyθ⟩ := h.exists_D₁_theta hB hV ha
  have htinv : d.t⁻¹ ∈ normalizer (d.D₁ : Set G) := inv_mem h.t_mem_normalizer_D₁
  refine ⟨d.t⁻¹ * y⁻¹ * d.t⁻¹⁻¹, (mem_normalizer_iff.mp htinv _).mp (inv_mem hy), ?_⟩
  have hy2 : d.t⁻¹ * (y * y) * d.t⁻¹⁻¹ ∈ d.V₁ :=
    (mem_normalizer_iff.mp (inv_mem h.t_mem_normalizer_V₁) _).mp (h.D₁_sq_mod hB hC hV hy)
  have e : (d.t * (d.t⁻¹ * y⁻¹ * d.t⁻¹⁻¹) * d.t⁻¹ * (d.t⁻¹ * y⁻¹ * d.t⁻¹⁻¹))⁻¹ * a =
      (d.t⁻¹ * (y * y) * d.t⁻¹⁻¹) * (a⁻¹ * d.theta y)⁻¹ :=
    calc (d.t * (d.t⁻¹ * y⁻¹ * d.t⁻¹⁻¹) * d.t⁻¹ * (d.t⁻¹ * y⁻¹ * d.t⁻¹⁻¹))⁻¹ * a
        = d.t⁻¹ * y * d.t * y * a := by group
      _ = d.t⁻¹ * y * d.t⁻¹ * y * a := by rw [h.t_inv]
      _ = (d.t⁻¹ * (y * y) * d.t⁻¹⁻¹) * (a⁻¹ * d.theta y)⁻¹ := by simp only [Data.theta]; group
  rw [e]
  exact mul_mem hy2 (inv_mem hyθ)

theorem exists_D₂_surj (h : Hyp d) (hB : HypB d) (hV : ∀ v ∈ d.V₁, v * v = 1) {a : G}
    (ha : a ∈ d.A₂) : ∃ x ∈ d.D₂, (x * (d.t * x * d.t⁻¹))⁻¹ * a ∈ d.D₁ := by
  obtain ⟨c, hc, hca⟩ := h.C₂_conj a ha
  have ht' : d.t⁻¹ = d.t := h.t_inv
  rw [h.C₂_eq_D₂_t hB, mem_sup_zpowers_of_normalizer h.t_mem_normalizer_D₂
    (by rw [h.t_sq]; exact one_mem _)] at hc
  rcases hc with hc | hc
  · refine ⟨c, hc, ?_⟩
    have hcc : c⁻¹ = c := inv_eq_of_mul_eq_one_right (h.D₂_sq hB hV hc)
    have e : c * (d.t * c * d.t⁻¹) = a := by
      calc c * (d.t * c * d.t⁻¹) = c⁻¹ * d.t * c * d.t⁻¹ := by rw [hcc]; group
        _ = a * d.t * d.t⁻¹ := by rw [hca]
        _ = a := by group
    rw [e, inv_mul_cancel]
    exact one_mem _
  · set x := c * d.t⁻¹ with hx_def
    refine ⟨x, hc, ?_⟩
    have hxx : x⁻¹ = x := inv_eq_of_mul_eq_one_right (h.D₂_sq hB hV hc)
    have haa : a⁻¹ = a := inv_eq_of_mul_eq_one_right (h.A₂_sq a ha)
    have hcx : c = x * d.t := by rw [hx_def]; group
    have e1 : d.t⁻¹ * x⁻¹ * d.t * x = a := by
      have := hca
      rw [hcx] at this
      calc d.t⁻¹ * x⁻¹ * d.t * x = (x * d.t)⁻¹ * d.t * (x * d.t) * d.t⁻¹ := by group
        _ = a * d.t * d.t⁻¹ := by rw [this]
        _ = a := by group
    have e : x * (d.t * x * d.t⁻¹) = a := by
      calc x * (d.t * x * d.t⁻¹) = x * (d.t * x * d.t) := by rw [ht']
        _ = x⁻¹ * d.t * x * d.t := by rw [hxx]; group
        _ = (d.t⁻¹ * x⁻¹ * d.t⁻¹ * x)⁻¹ := by group
        _ = (d.t⁻¹ * x⁻¹ * d.t * x)⁻¹ := by rw [ht']
        _ = a := by rw [e1, haa]
    rw [e, inv_mul_cancel]
    exact one_mem _

section Main

variable {θ : d.K₁ ≃* SU42b} {ιG : (Fin 8 → ZMod 2) → G}

theorem y13Hyp_of (h : Hyp d) (hB : HypB d) (hC : HypC d) (hV : ∀ v ∈ d.V₁, v * v = 1)
    (h416 : Hyp416 d) (hc : Y13Coords d θ ιG) (hKA : d.K₁ ⊓ d.A₁ = ⊥)
    (hN : d.D₂ ≤ normalizer (d.D₁ : Set G) ∧ d.D₁ ≤ normalizer (d.D₂ : Set G)) :
    YamadaPar.Y13Hyp d.t d.D₁ d.V₁ d.A₁ d.K₁ d.D₂ θ ιG where
  t_sq := h.t_sq
  sec := elemSec h hB hC hV
  card_D₁ := h.card_D₁ hB hV
  card_V₁ := h.card_V₁
  V₁_sq := hV
  D₁_nonab := D₁_nonab h hB hV
  K₁_norm := h.K₁_le_XV.trans Hyp.XV_le_normalizer_D₁
  K₁_cent := fun k hk v hv => by
    rw [← mem_centralizer_iff.mp (h.K₁_le_cent_V₁ hk) v hv, mul_inv_cancel_right]
  K₁_t := fun k hk => t_comm_of_mem_L h (h.K₁_le_L hk)
  D₂_comm := fun x hx y hy => h.D₂_comm hB hx hy
  V₁_le_D₂ := h.V₁_le_D₂
  D₂_norm := hN.1
  t_D₁ := h.t_mem_normalizer_D₁
  t_D₂ := h.t_mem_normalizer_D₂
  t_V₁ := h.t_mem_normalizer_V₁
  card_D₁D₂ := (h.card_D₁_inf_D₂ hB hV).ge
  card_D₂ := h.card_D₂ hB
  A₁_le := h.A₁_le_D₁ hB hV
  A₁_t := fun a ha => t_comm_of_mem_L h (h.A₁_le_L ha)
  D₁_H := fun x hx hxt => mem_A₁_of_comm h hB hV hx hxt
  ι_mem := hc.ι_mem
  ι_add := fun u v => zpowers_z_le_V₁ h (hc.ι_add u v)
  ι_inj := fun u hu => hc.ι_inj u (mem_zpowers_of_mem_A₁ h (hc.ι_mem u) hu)
  ι_range := fun u => exists_ι_range h hB hC hV (hc.ι_mem u)
  K₁_ι := fun k u => zpowers_z_le_V₁ h (hc.K₁_ι k u)
  E_mem := fun m hm => ⟨_, h.A₂_le_D₂ (hc.E_mem m hm), by rw [inv_mul_cancel]; exact one_mem _⟩
  ν_norm := fun j hj =>
    (sup_le (h.K₂_le_normalizer_D₂ hB) (h.A₂_le_D₂.trans le_normalizer)) (hc.ν_mem j hj)
  W0 := fun y hy x hx hxe => by
    have hxC : x ∈ centE θ (elemSec h hB hC hV) (h.K₁_le_XV.trans Hyp.XV_le_normalizer_D₁) :=
      ⟨hx, hxe⟩
    rw [centE_eq h hB hC hV hc] at hxC
    rw [h.D₂_comm hB hy (mem_inf.mp hxC).2, mul_inv_cancel_right, inv_mul_cancel]
    exact one_mem _
  W1 := fun y hy x hx m hm => by
    have hyx := mem_D₂_of_comm h hB hC hV hN.2 hy hx
    rw [h.D₂_comm hB (h.A₂_le_D₂ (hc.E_mem m hm)) hyx, mul_inv_cancel_right, inv_mul_cancel]
    exact one_mem _
  D₂_fix := fun x hx hk => exists_eG_of_kap_mem h hB hV h416 hc hKA hx hk
  D₂_surj := fun m hm => exists_D₂_surj h hB hV (hc.E_mem m hm)
  Dinj := fun x hx hT => mem_D₁_of_trivW h hB hC hV h416 hc hKA hN.1 hx hT
  Kr := fun x hx hT htx => mem_D₁_of_kr h hB hC hV hc hN.1 hx hT htx

end Main

end CFSG.EvenSmallLie.UnitarySix.Child5
