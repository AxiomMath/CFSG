module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaQNF
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDNormal

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaD

open Subgroup CFSG.EvenSmallLie.UnitarySix.YamadaQ
open scoped commutatorElement

variable {G : Type*} [Group G]

namespace Hyp

variable [Finite G] {d : Data G} (h : Hyp d) (hB : HypB d) (hV : ∀ v ∈ d.V₁, v * v = 1)
  (hQ : HypQ d)
include h hB hV hQ

omit [Finite G] hB hV in
theorem theta_conjG {y : G} : d.theta (d.w₂₃₂ * y * d.w₂₃₂⁻¹) =
    d.w₂₃₂ * d.theta y * d.w₂₃₂⁻¹ := by
  have hc : Commute d.w₂₃₂ d.t := h.w₂₃₂_comm_t hQ
  simp only [Data.theta]
  calc (d.w₂₃₂ * y * d.w₂₃₂⁻¹)⁻¹ * d.t * (d.w₂₃₂ * y * d.w₂₃₂⁻¹) * d.t
      = d.w₂₃₂ * y⁻¹ * (d.w₂₃₂⁻¹ * d.t) * d.w₂₃₂ * y * (d.w₂₃₂⁻¹ * d.t) := by group
    _ = d.w₂₃₂ * y⁻¹ * (d.t * d.w₂₃₂⁻¹) * d.w₂₃₂ * y * (d.t * d.w₂₃₂⁻¹) := by
        rw [hc.inv_left.eq]
    _ = d.w₂₃₂ * (y⁻¹ * d.t * y * d.t) * d.w₂₃₂⁻¹ := by group

omit hB hV in
theorem X₁_le_conjG_V₂ : d.X₁ ≤ d.conjG d.V₂ := by
  intro x hx
  have h1 := h.w₂₃₂_X₁ hQ hx
  rw [mem_conjG]
  rw [w₂₃₂_inv hQ] at h1 ⊢
  exact h.Z₂S_le_V₂ (mem_sup_left h1)

omit hB hV in
theorem exists_conjG_V₂_theta {x : G} (hx : x ∈ d.X₁) :
    ∃ y ∈ d.conjG d.V₂, d.theta y = x := by
  have hb : d.w₂₃₂⁻¹ * x * d.w₂₃₂ ∈ d.Z₂S := by
    have h1 := h.w₂₃₂_X₁ hQ hx
    rw [w₂₃₂_inv hQ] at h1 ⊢
    exact mem_sup_left h1
  obtain ⟨y', hy', hθ'⟩ := h.exists_V₂_conj hb
  refine ⟨d.w₂₃₂ * y' * d.w₂₃₂⁻¹, ⟨y', hy', rfl⟩, ?_⟩
  rw [h.theta_conjG hQ]
  change d.w₂₃₂ * (y'⁻¹ * d.t * y' * d.t) * d.w₂₃₂⁻¹ = x
  rw [hθ']; group

omit hB hV in
theorem AV_inf_cent_e_le {x : G} (hx : x ∈ d.AV) (hxe : x * d.e = d.e * x) :
    x ∈ d.V₂ ⊔ d.conjG d.V₂ := by
  obtain ⟨a, ha, v, hv, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (fun a ha w hw => (mem_centralizer_iff.mp (h.V₁_le_cent_A₁ hw) a ha)) hx
  have hve : v * d.e = d.e * v :=
    mem_centralizer_singleton_iff.mp (h.V₂_le_cent_e (d.V₁_le_V₂ hv))
  have hae : a * d.e = d.e * a := by
    have e1 : a = (a * v) * v⁻¹ := by group
    have hve' : v⁻¹ * d.e = d.e * v⁻¹ := (Commute.inv_left hve).eq
    calc a * d.e = (a * v) * (v⁻¹ * d.e) := by group
      _ = (a * v) * d.e * v⁻¹ := by rw [hve']; group
      _ = d.e * (a * v) * v⁻¹ := by rw [hxe]
      _ = d.e * a := by group
  obtain ⟨y, hy, b, hb, rfl⟩ := hQ.CA₁e a ha hae
  exact mul_mem (mul_mem (mem_sup_right (h.X₁_le_conjG_V₂ hQ hy)) (mem_sup_left
    (h.Z₂S_le_V₂ hb))) (mem_sup_left (d.V₁_le_V₂ hv))

theorem E₁_le_sup : d.D₁ ⊓ centralizer ({d.e} : Set G) ≤ d.V₂ ⊔ d.conjG d.V₂ := by
  have := h.V₁_normal_AV
  intro u ⟨huD, hue⟩
  have hue' : u * d.e = d.e * u := mem_centralizer_singleton_iff.mp hue
  have hθu := h.crossed_D₁ hB hV huD
  obtain ⟨a, ha, v, hv, hav⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (fun a ha w hw => (mem_centralizer_iff.mp (h.V₁_le_cent_A₁ hw) a ha)) hθu
  have hte : d.t * d.e = d.e * d.t := h.e_comm_t.symm
  have hθe : d.theta u * d.e = d.e * d.theta u := by
    have : d.theta u ∈ centralizer ({d.e} : Set G) := by
      simp only [Data.theta]
      have ht : d.t ∈ centralizer ({d.e} : Set G) := mem_centralizer_singleton_iff.mpr hte
      exact mul_mem (mul_mem (mul_mem (inv_mem hue) ht) hue) ht
    exact mem_centralizer_singleton_iff.mp this
  have hve : v * d.e = d.e * v :=
    mem_centralizer_singleton_iff.mp (h.V₂_le_cent_e (d.V₁_le_V₂ hv))
  have hae : a * d.e = d.e * a := by
    have hve' : v⁻¹ * d.e = d.e * v⁻¹ := (Commute.inv_left hve).eq
    have e1 : a = d.theta u * v⁻¹ := by rw [← hav]; group
    rw [e1]
    calc d.theta u * v⁻¹ * d.e = d.theta u * (v⁻¹ * d.e) := by group
      _ = d.theta u * d.e * v⁻¹ := by rw [hve']; group
      _ = d.e * (d.theta u * v⁻¹) := by rw [hθe]; group
  obtain ⟨x, hx, b, hb, rfl⟩ := hQ.CA₁e a ha hae
  obtain ⟨y₁, hy₁, hθ₁⟩ := h.exists_V₂_conj hb
  obtain ⟨y₂, hy₂, hθ₂⟩ := h.exists_conjG_V₂_theta hQ hx
  set w := y₂ * y₁ with hw
  have hwE : w ∈ d.D₁ ⊓ centralizer ({d.e} : Set G) :=
    mul_mem (h.conjG_V₂_le_E₁ hQ hB hV hy₂) (h.V₂_le_E₁ hB hV hy₁)
  have hU : ∀ {z : G}, z ∈ d.D₁ → z ∈ d.U₁ := fun hz => h.D₁_le_U₁ hB hV hz
  have hbA : b ∈ d.A₁ := (h.Z₂S_le_A₁) hb
  have hxA : x ∈ d.A₁ := by
    have : x = (x * b) * b⁻¹ := by group
    rw [this]; exact mul_mem ha (inv_mem hbA)
  have hAV : ∀ {z : G}, z ∈ d.A₁ → z ∈ d.AV := fun hz => mem_sup_left hz
  have c1 : d.cls (d.theta u) = d.cls x * d.cls b := by
    rw [← hav, cls_mul (hAV ha) (mem_sup_right hv), (cls_eq_one_iff (mem_sup_right hv)).mpr hv,
      mul_one, cls_mul (hAV hxA) (hAV hbA)]
  have c2 : d.cls (d.theta w) = d.cls x * d.cls b := by
    rw [hw, h.cls_theta_mul (hU (h.conjG_V₂_le_E₁ hQ hB hV hy₂).1)
      (hU (h.V₂_le_D₁ hB hV hy₁)), hθ₂]
    simp only [Data.theta] at hθ₁ ⊢
    rw [hθ₁]
  have huw : u * w⁻¹ ∈ d.AV := by
    have hD : u * w⁻¹ ∈ d.D₁ := mul_mem huD (inv_mem hwE.1)
    rw [← h.theta_mem_V₁_iff hB hV hD, ← cls_eq_one_iff (h.crossed_D₁ hB hV hD),
      h.cls_theta_mul (hU huD) (hU (inv_mem hwE.1)), h.cls_theta_inv (hU hwE.1), c1, c2,
      mul_inv_cancel]
  have huwe : u * w⁻¹ * d.e = d.e * (u * w⁻¹) := by
    have hwe := mem_centralizer_singleton_iff.mp hwE.2
    have hwe' : w⁻¹ * d.e = d.e * w⁻¹ := (Commute.inv_left hwe).eq
    calc u * w⁻¹ * d.e = u * (w⁻¹ * d.e) := by group
      _ = u * d.e * w⁻¹ := by rw [hwe']; group
      _ = d.e * (u * w⁻¹) := by rw [hue']; group
  have h1 := h.AV_inf_cent_e_le hQ huw huwe
  have e2 : u = (u * w⁻¹) * w := by group
  rw [e2]
  exact mul_mem h1 (mul_mem (mem_sup_right hy₂) (mem_sup_left hy₁))

omit hB hV hQ in
theorem exists_comm_j₀ {y : G} (hy : y ∈ ⁅d.D₄, d.J⁆) :
    ∃ y' ∈ ⁅d.D₄, d.J⁆, ⁅y', d.j₀⁆ = y := by
  let f : (⁅d.D₄, d.J⁆ : Subgroup G) → (⁅d.D₄, d.J⁆ : Subgroup G) := fun y' =>
    ⟨⁅(y' : G), d.j₀⁆, commutator_mem_commutator (h.comm_D₄_J_le y'.2) h.j₀_mem_J⟩
  have hf : Function.Injective f := by
    intro y₁ y₂ h12
    have e : (y₁ : G) * d.j₀ * (y₁ : G)⁻¹ * d.j₀⁻¹ = (y₂ : G) * d.j₀ * (y₂ : G)⁻¹ * d.j₀⁻¹ := by
      have := congrArg Subtype.val h12
      simpa [f, commutatorElement_def] using this
    have e' : (y₁ : G) * d.j₀ * (y₁ : G)⁻¹ = (y₂ : G) * d.j₀ * (y₂ : G)⁻¹ :=
      mul_right_cancel e
    have hc : d.j₀ * ((y₂ : G)⁻¹ * y₁) = ((y₂ : G)⁻¹ * y₁) * d.j₀ := by
      calc d.j₀ * ((y₂ : G)⁻¹ * y₁) = (y₂ : G)⁻¹ * ((y₂ : G) * d.j₀ * (y₂ : G)⁻¹) * y₁ := by
            group
        _ = (y₂ : G)⁻¹ * ((y₁ : G) * d.j₀ * (y₁ : G)⁻¹) * y₁ := by rw [e']
        _ = ((y₂ : G)⁻¹ * y₁) * d.j₀ := by group
    have h1 := h.comm_D₄_J_inf_cent (mul_mem (inv_mem y₂.2) y₁.2) hc
    exact Subtype.ext (by rw [← mul_left_cancel_iff (a := (y₂ : G)⁻¹), h1, inv_mul_cancel])
  obtain ⟨y', hy'⟩ := (Finite.injective_iff_surjective.mp hf) ⟨y, hy⟩
  exact ⟨y', y'.2, congrArg Subtype.val hy'⟩

theorem conjG_V₂_le_comm :
    d.conjG d.V₂ ≤ ⁅d.D₁ ⊓ centralizer ({d.e} : Set G), d.J⁆ ⊔ d.V₂ := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨c, hc, v, hv, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (fun a ha w hw => h.D₄_comm (h.comm_D₄_J_le ha) (V₁_le_D₄ hw)) hy
  obtain ⟨c', hc', rfl⟩ := h.exists_comm_j₀ hc
  have hgv : d.w₂₃₂ * v * d.w₂₃₂⁻¹ = v := by
    rw [(mem_centralizer_iff.mp (h.K₁_le_cent_V₁ hQ.w₂₃₂_mem_K₁) v hv).symm,
      mul_inv_cancel_right]
  have hgj : d.w₂₃₂ * d.j₀ * d.w₂₃₂⁻¹ = d.j₀ := by
    rw [hQ.w₂₃₂_comm_j₀, mul_inv_cancel_right]
  change d.w₂₃₂ * (⁅c', d.j₀⁆ * v) * d.w₂₃₂⁻¹ ∈ _
  have e : d.w₂₃₂ * (⁅c', d.j₀⁆ * v) * d.w₂₃₂⁻¹ =
      ⁅d.w₂₃₂ * c' * d.w₂₃₂⁻¹, d.j₀⁆ * (d.w₂₃₂ * v * d.w₂₃₂⁻¹) := by
    rw [← hgj, ← conjugate_commutatorElement, hgj]; group
  rw [e, hgv]
  have hc'E : d.w₂₃₂ * c' * d.w₂₃₂⁻¹ ∈ d.D₁ ⊓ centralizer ({d.e} : Set G) :=
    h.conjG_V₂_le_E₁ hQ hB hV ⟨c', (le_sup_left : ⁅d.D₄, d.J⁆ ≤ d.V₂) hc', rfl⟩
  exact mul_mem (mem_sup_left (commutator_mem_commutator hc'E h.j₀_mem_J))
    (mem_sup_right (d.V₁_le_V₂ hv))

theorem E₁_le_comm_sup :
    d.D₁ ⊓ centralizer ({d.e} : Set G) ≤ ⁅d.D₁ ⊓ centralizer ({d.e} : Set G), d.J⁆ ⊔ d.V₂ :=
  (h.E₁_le_sup hB hV hQ).trans (sup_le le_sup_right (h.conjG_V₂_le_comm hB hV hQ))

end Hyp

end CFSG.EvenSmallLie.UnitarySix.YamadaD
