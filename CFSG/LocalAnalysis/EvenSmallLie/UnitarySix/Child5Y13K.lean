module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.Child5Y13D

public section

namespace CFSG.EvenSmallLie.UnitarySix.Child5

open Subgroup Matrix YamadaPar YamadaD

variable {G : Type} [Group G] [Finite G] {d : YamadaD.Data G}

theorem theta_mem_D₁ (h : Hyp d) {w : G} (hw : w ∈ d.D₁) : d.theta w ∈ d.D₁ := by
  have h1 := t_conj_mem_of_normalizer h.t_mem_normalizer_D₁ hw
  rw [h.t_inv] at h1
  simp only [Data.theta]
  rw [mul_assoc, mul_assoc]
  exact mul_mem (inv_mem hw) (by rw [← mul_assoc]; exact h1)

omit [Finite G] in
theorem t_theta_t (h : Hyp d) (w : G) : d.t * d.theta w * d.t = (d.theta w)⁻¹ := by
  calc d.t * d.theta w * d.t = d.t * w⁻¹ * d.t * w * (d.t * d.t) := by
        simp only [Data.theta]; group
    _ = d.t⁻¹ * w⁻¹ * d.t⁻¹ * w := by rw [h.t_sq, mul_one, h.t_inv]
    _ = (d.theta w)⁻¹ := by simp only [Data.theta]; group

theorem exists_theta_eq (h : Hyp d) (hB : HypB d) (hC : HypC d) (hV : ∀ v ∈ d.V₁, v * v = 1)
    {c : G} (hc : c ∈ d.D₁) (hct : d.t * c * d.t = c⁻¹) : ∃ w ∈ d.D₁, d.theta w = c := by
  have hs := elemSec h hB hC hV
  have ht' : d.t⁻¹ = d.t := h.t_inv
  have hθc : d.theta c ∈ d.V₁ := by
    have e : d.theta c = (c * c)⁻¹ :=
      calc d.theta c = c⁻¹ * (d.t * c * d.t) := by simp only [Data.theta]; group
        _ = (c * c)⁻¹ := by rw [hct]; group
    rw [e]
    exact inv_mem (hs.sq c hc)
  have hcAV : c ∈ d.AV := (h.theta_mem_V₁_iff hB hV hc).mp hθc
  obtain ⟨a, ha, v, hv, hav⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (fun a ha v hv => (mem_centralizer_iff.mp (h.V₁_le_cent_A₁ hv) a ha)) hcAV
  obtain ⟨w, hw, haw⟩ := h.exists_D₁_theta hB hV ha
  have hθw := theta_mem_D₁ h hw
  set r := (d.theta w)⁻¹ * c with hr_def
  have hr : r ∈ d.V₁ := by
    have e : r = (a⁻¹ * d.theta w)⁻¹ * v := by rw [hr_def, ← hav]; group
    rw [e]
    exact mul_mem (inv_mem haw) hv
  have hrc : c = d.theta w * r := by rw [hr_def]; group
  have hrt : d.t * r * d.t = r := by
    have e1 : d.t * r * d.t = (d.t * (d.theta w)⁻¹ * d.t) * (d.t * c * d.t) :=
      calc d.t * r * d.t = d.t * (d.theta w)⁻¹ * (d.t * d.t) * c * d.t := by
            rw [h.t_sq, hr_def]; group
        _ = (d.t * (d.theta w)⁻¹ * d.t) * (d.t * c * d.t) := by group
    have e2 : d.t * (d.theta w)⁻¹ * d.t = d.theta w :=
      calc d.t * (d.theta w)⁻¹ * d.t = (d.t⁻¹ * d.theta w * d.t⁻¹)⁻¹ := by group
        _ = (d.t * d.theta w * d.t)⁻¹ := by rw [ht']
        _ = d.theta w := by rw [t_theta_t h, inv_inv]
    have hc' : r⁻¹ * (d.theta w)⁻¹ = (d.theta w)⁻¹ * r⁻¹ :=
      hs.central _ (inv_mem hr) _ (inv_mem hθw)
    rw [e1, e2, hct, hrc]
    calc d.theta w * (d.theta w * r)⁻¹ = d.theta w * (r⁻¹ * (d.theta w)⁻¹) := by group
      _ = d.theta w * ((d.theta w)⁻¹ * r⁻¹) := by rw [hc']
      _ = r⁻¹ := by group
      _ = r := (eq_inv_of_mul_eq_one_left (hV r hr)).symm
  have hrz : r ∈ zpowers d.z := by
    rw [← h.V₁_inf_H]
    refine mem_inf.mpr ⟨hr, mem_centralizer_singleton_iff.mpr ?_⟩
    calc r * d.t = d.t⁻¹ * (d.t * r * d.t) := by group
      _ = d.t * r := by rw [hrt, ht']
  rcases h.mem_zpowers_z_iff.mp hrz with hr1 | hrz'
  · exact ⟨w, hw, by rw [hrc, hr1, mul_one]⟩
  · obtain ⟨v₀, hv₀, hv₀z⟩ := h.exists_V₁_not_mem_z
    refine ⟨w * v₀, mul_mem hw (hs.le hv₀), ?_⟩
    rw [Hyp.theta_mul h.t_sq]
    have hcv : v₀⁻¹ * d.theta w = d.theta w * v₀⁻¹ := hs.central _ (inv_mem hv₀) _ hθw
    have hθv : d.theta v₀ = d.z := h.crossed_V₁_eq_z hv₀ hv₀z
    rw [hcv, inv_mul_cancel_right, hθv, hrc, hrz']

theorem nOne_le_normalizer_D₁ (h : Hyp d) (hN : d.D₂ ≤ normalizer (d.D₁ : Set G)) :
    YamadaPar.nOne d.D₁ d.K₁ d.D₂ ≤ normalizer (d.D₁ : Set G) :=
  sup_le (sup_le le_normalizer (h.K₁_le_XV.trans Hyp.XV_le_normalizer_D₁)) hN

theorem nOne_le_normalizer_V₁ (h : Hyp d) (hB : HypB d) (hs : YamadaPar.ElemSec d.D₁ d.V₁) :
    YamadaPar.nOne d.D₁ d.K₁ d.D₂ ≤ normalizer (d.V₁ : Set G) := by
  refine sup_le (sup_le (fun x hx => YamadaPar.mem_normalizer_of_conj_eq fun v hv => ?_)
    (fun k hk => YamadaPar.mem_normalizer_of_conj_eq fun v hv => ?_)) (D₂_le_normalizer_V₁ h hB)
  · rw [← hs.central v hv x hx, mul_inv_cancel_right]
  · rw [← mem_centralizer_iff.mp (h.K₁_le_cent_V₁ hk) v hv, mul_inv_cancel_right]

section Kr

variable {θ : d.K₁ ≃* SU42b} {ιG : (Fin 8 → ZMod 2) → G}

theorem not_trivW_t (h : Hyp d) (hB : HypB d) (hV : ∀ v ∈ d.V₁, v * v = 1)
    (hc : Y13Coords d θ ιG) : ¬ TrivW d d.t := by
  intro hT
  set u₀ : Fin 8 → ZMod 2 := Pi.single 0 1
  have hu₀ : u₀ ≠ 0 := by
    intro h0
    have := congrFun h0 0
    simp [u₀] at this
  have ha₀ : ιG u₀ ∉ d.V₁ := fun hV₁ =>
    hu₀ (hc.ι_inj _ (mem_zpowers_of_mem_A₁ h (hc.ι_mem u₀) hV₁))
  obtain ⟨x₀, hx₀, hθ⟩ := h.exists_D₁_theta hB hV (hc.ι_mem u₀)
  apply ha₀
  have h1 := hT x₀ hx₀
  have h2 : d.theta x₀ ∈ d.V₁ := by
    have e : d.theta x₀ = ((d.t * x₀ * d.t⁻¹)⁻¹ * x₀)⁻¹ := by
      simp only [Data.theta]; rw [h.t_inv]; group
    rw [e]
    exact inv_mem h1
  rw [show ιG u₀ = d.theta x₀ * ((ιG u₀)⁻¹ * d.theta x₀)⁻¹ by group]
  exact mul_mem h2 (inv_mem hθ)

theorem mem_D₁_of_kr (h : Hyp d) (hB : HypB d) (hC : HypC d) (hV : ∀ v ∈ d.V₁, v * v = 1)
    (hc : Y13Coords d θ ιG) (hN : d.D₂ ≤ normalizer (d.D₁ : Set G)) {x : G}
    (hx : x ∈ YamadaPar.nOne d.D₁ d.K₁ d.D₂) (hT : TrivW d x)
    (htx : d.t * x * d.t⁻¹ * x⁻¹ ∈ d.D₁) : x ∈ d.D₁ := by
  have hs := elemSec h hB hC hV
  have ht' : d.t⁻¹ = d.t := h.t_inv
  have hxV := nOne_le_normalizer_V₁ h hB hs hx
  have hxD := nOne_le_normalizer_D₁ h hN hx
  have hcD : d.theta x ∈ d.D₁ := by
    have h1 := (mem_normalizer_iff.mp (inv_mem hxD) _).mp htx
    have e : d.theta x = x⁻¹ * (d.t * x * d.t⁻¹ * x⁻¹) * x⁻¹⁻¹ := by
      simp only [Data.theta]; rw [ht']; group
    rw [e]
    exact h1
  obtain ⟨w, hw, hwc⟩ := exists_theta_eq h hB hC hV hcD (t_theta_t h x)
  set x' := x * w⁻¹ with hx'_def
  have hx't : d.t * x' = x' * d.t := by
    have e1 : x⁻¹ * d.t * x * d.t = w⁻¹ * d.t * w * d.t := hwc.symm
    calc d.t * x' = x * (x⁻¹ * d.t * x * d.t) * d.t⁻¹ * w⁻¹ := by rw [hx'_def]; group
      _ = x * (w⁻¹ * d.t * w * d.t) * d.t⁻¹ * w⁻¹ := by rw [e1]
      _ = x' * d.t := by rw [hx'_def]; group
  have hwN : w ∈ YamadaPar.nOne d.D₁ d.K₁ d.D₂ :=
    mem_sup_left (mem_sup_left hw : w ∈ d.D₁ ⊔ d.K₁)
  have hx'N : x' ∈ YamadaPar.nOne d.D₁ d.K₁ d.D₂ := mul_mem hx (inv_mem hwN)
  have hx'D := nOne_le_normalizer_D₁ h hN hx'N
  have hx'V := nOne_le_normalizer_V₁ h hB hs hx'N
  have hTx' : TrivW d x' := trivW_mul hxV hT (trivW_of_mem hs (inv_mem hw))
  have hx'H : x' ∈ d.H := mem_centralizer_singleton_iff.mpr hx't.symm
  have hx't' : d.t * x'⁻¹ = x'⁻¹ * d.t := by
    calc d.t * x'⁻¹ = x'⁻¹ * (x' * d.t) * x'⁻¹ := by group
      _ = x'⁻¹ * (d.t * x') * x'⁻¹ := by rw [hx't]
      _ = x'⁻¹ * d.t := by group
  have hx'A : x' ∈ normalizer (d.A₁ : Set G) := by
    apply mem_normalizer_of_conj_mem
    intro a ha
    have haD := h.A₁_le_D₁ hB hV ha
    refine mem_A₁_of_comm h hB hV ((mem_normalizer_iff.mp hx'D a).mp haD) ?_
    have hat : d.t * a = a * d.t := t_comm_of_mem_L h (h.A₁_le_L ha)
    calc d.t * (x' * a * x'⁻¹) = (d.t * x') * a * x'⁻¹ := by group
      _ = x' * (d.t * a) * x'⁻¹ := by rw [hx't]; group
      _ = x' * a * (d.t * x'⁻¹) := by rw [hat]; group
      _ = x' * a * x'⁻¹ * d.t := by rw [hx't']; group
  have hcomm : ∀ a ∈ d.A₁, x' * a * x'⁻¹ * a⁻¹ ∈ zpowers d.z := by
    intro a ha
    have haD := h.A₁_le_D₁ hB hV ha
    set u := (x' * a * x'⁻¹)⁻¹ * a with hu_def
    have hu : u ∈ d.V₁ := hTx' a haD
    have hcen : u⁻¹ * a = a * u⁻¹ := hs.central _ (inv_mem hu) a haD
    have e : x' * a * x'⁻¹ * a⁻¹ = u⁻¹ :=
      calc x' * a * x'⁻¹ * a⁻¹ = a * u⁻¹ * a⁻¹ := by rw [hu_def]; group
        _ = u⁻¹ * a * a⁻¹ := by rw [hcen]
        _ = u⁻¹ := by group
    rw [← h.V₁_inf_H]
    refine mem_inf.mpr ⟨e ▸ inv_mem hu, ?_⟩
    have haH := h.L_le_H (h.A₁_le_L ha)
    exact mul_mem (mul_mem (mul_mem hx'H haH) (inv_mem hx'H)) (inv_mem haH)
  rcases (h.mem_withT_iff h.A₁_le_L).mp (hB.CH_A₁_mod x' hx'H hx'A hcomm) with hA | hAt
  · have e : x = x' * w := by rw [hx'_def]; group
    rw [e]
    exact mul_mem (h.A₁_le_D₁ hB hV hA) hw
  · exfalso
    apply not_trivW_t h hB hV hc
    have e : d.t = x'⁻¹ * (x' * d.t) := by group
    rw [e]
    exact trivW_mul (inv_mem hx'V) (trivW_inv hx'D hTx')
      (trivW_of_mem hs (h.A₁_le_D₁ hB hV hAt))

end Kr

end CFSG.EvenSmallLie.UnitarySix.Child5
