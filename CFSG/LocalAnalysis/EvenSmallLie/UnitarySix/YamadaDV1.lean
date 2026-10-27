module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDD4

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaD

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

namespace Hyp

variable {d : Data G} (h : Hyp d)
include h

omit h in
theorem V₁_le_D₄ : d.V₁ ≤ d.D₄ := inf_le_left

omit h in
theorem V₁_le_cent_X₁ : d.V₁ ≤ centralizer (d.X₁ : Set G) := inf_le_right

theorem V₁_le_D [Finite G] : d.V₁ ≤ d.D := V₁_le_D₄.trans h.D₄_le_D

theorem V₁_le_cent_A₃ [Finite G] : d.V₁ ≤ centralizer (d.A₃ : Set G) :=
  h.V₁_le_D.trans h.D_le_cent_A₃

theorem V₁_le_cent_A₁ [Finite G] : d.V₁ ≤ centralizer (d.A₁ : Set G) := by
  intro v hv
  have h1 : v ∈ centralizer ((d.X₁ ⊔ d.A₃ : Subgroup G) : Set G) :=
    mem_centralizer_sup (V₁_le_cent_X₁ hv) (h.V₁_le_cent_A₃ hv)
  exact centralizer_le h.A₁_le h1

theorem V₁_comm [Finite G] {v w : G} (hv : v ∈ d.V₁) (hw : w ∈ d.V₁) : v * w = w * v :=
  h.D₄_comm (V₁_le_D₄ hv) (V₁_le_D₄ hw)

theorem z_mem_V₁ [Finite G] : d.z ∈ d.V₁ :=
  mem_inf.mpr ⟨h.A₄_le_D₄ h.z_mem_A₄, h.z_cent_X₁⟩

theorem z_sq : d.z * d.z = 1 := h.A₄_sq h.z_mem_A₄

theorem z_comm_t : d.z * d.t = d.t * d.z := h.comm_of_mem_L (h.A₄_le_L h.z_mem_A₄)

theorem card_zpowers_z : Nat.card (zpowers d.z) = 2 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [sq]; exact h.z_sq) h.z_ne_one

theorem mem_zpowers_z_iff {x : G} : x ∈ zpowers d.z ↔ x = 1 ∨ x = d.z := by
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
    have ho : orderOf d.z = 2 := orderOf_eq_prime (by rw [sq]; exact h.z_sq) h.z_ne_one
    rw [← zpow_mod_orderOf, ho]
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · left; rw [Nat.cast_ofNat, hk, zpow_zero]
    · right; rw [Nat.cast_ofNat, hk, zpow_one]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _

theorem V₁_inf_H_le [Finite G] : d.V₁ ⊓ d.H ≤ zpowers d.z := by
  intro x hx
  obtain ⟨hxV, hxH⟩ := mem_inf.mp hx
  have hxA : x ∈ d.A₄ := by
    rw [← h.D₄_inf_H]; exact mem_inf.mpr ⟨V₁_le_D₄ hxV, hxH⟩
  exact h.A₄_cent_X₁ (mem_inf.mpr ⟨hxA, V₁_le_cent_X₁ hxV⟩)

theorem crossed_V₁ [Finite G] {v : G} (hv : v ∈ d.V₁) : v⁻¹ * d.t * v * d.t ∈ zpowers d.z := by
  have hcA := h.crossed_X₄ (D_le_X₄ (h.V₁_le_D hv))
  refine h.A₄_cent_X₁ (mem_inf.mpr ⟨hcA, mem_centralizer_iff.mpr fun x hx => ?_⟩)
  have hxt : x * d.t = d.t * x := h.comm_of_mem_L (h.Λ_le_L (h.X₁_le_Λ hx))
  have hxv : x * v = v * x := (mem_centralizer_iff.mp (V₁_le_cent_X₁ hv) x hx)
  have := crossed_conj (x := v) hxt
  rw [show x * v * x⁻¹ = v by rw [hxv]; group] at this
  calc x * (v⁻¹ * d.t * v * d.t) = x * (v⁻¹ * d.t * v * d.t) * x⁻¹ * x := by group
    _ = (v⁻¹ * d.t * v * d.t) * x := by rw [← this]

theorem exists_V₁_conj [Finite G] : ∃ v ∈ d.V₁, v⁻¹ * d.t * v = d.z * d.t := by
  have hu₁ := h.u₁_mem
  have hu₂ := h.u₂_mem
  have hX₁ := h.X₁_le_closure
  have hu₁2 := h.u₁_sq
  have hu₂2 := h.u₂_sq
  have hu₁₂ := h.u₁_comm_u₂
  have ha₀ := h.a₀_mem
  have hnorm := h.norm_a₀
  set u₁ := d.u₁
  set u₂ := d.u₂
  set a₀ := d.a₀
  obtain ⟨d₀, hd₀, hd₀t⟩ := h.exists_D₄_conj ha₀
  have hconj : ∀ x ∈ d.X₁, x * d₀ * x⁻¹ ∈ d.D₄ := fun x hx => (mem_normalizer_iff.mp
    (h.Λ_le_normalizer_D₄ (h.X₁_le_Λ hx)) d₀).mp hd₀
  have hc : ∀ {a b : G}, a ∈ d.D₄ → b ∈ d.D₄ → a * b = b * a := fun ha hb => h.D₄_comm ha hb
  obtain ⟨f₂, hf₂⟩ : ∃ f, f = u₁ * d₀ * u₁⁻¹ := ⟨_, rfl⟩
  obtain ⟨f₃, hf₃⟩ : ∃ f, f = u₂ * d₀ * u₂⁻¹ := ⟨_, rfl⟩
  obtain ⟨f₄, hf₄⟩ : ∃ f, f = (u₁ * u₂) * d₀ * (u₁ * u₂)⁻¹ := ⟨_, rfl⟩
  have h₂ : f₂ ∈ d.D₄ := hf₂ ▸ hconj u₁ hu₁
  have h₃ : f₃ ∈ d.D₄ := hf₃ ▸ hconj u₂ hu₂
  have h₄ : f₄ ∈ d.D₄ := hf₄ ▸ hconj _ (mul_mem hu₁ hu₂)
  have hnD : d₀ * f₂ * f₃ * f₄ ∈ d.D₄ := mul_mem (mul_mem (mul_mem hd₀ h₂) h₃) h₄
  have hn₁ : u₁ * (d₀ * f₂ * f₃ * f₄) * u₁⁻¹ = d₀ * f₂ * f₃ * f₄ := by
    have e2 : u₁ * f₂ * u₁⁻¹ = d₀ := by
      rw [hf₂, show u₁ * (u₁ * d₀ * u₁⁻¹) * u₁⁻¹ = (u₁ * u₁) * d₀ * (u₁ * u₁)⁻¹ by group,
        hu₁2]; group
    have e3 : u₁ * f₃ * u₁⁻¹ = f₄ := by rw [hf₃, hf₄]; group
    have e4 : u₁ * f₄ * u₁⁻¹ = f₃ := by
      rw [hf₄, hf₃, show u₁ * ((u₁ * u₂) * d₀ * (u₁ * u₂)⁻¹) * u₁⁻¹ =
        (u₁ * u₁) * u₂ * d₀ * ((u₁ * u₁) * u₂)⁻¹ by group, hu₁2]; group
    calc u₁ * (d₀ * f₂ * f₃ * f₄) * u₁⁻¹ = (u₁ * d₀ * u₁⁻¹) * (u₁ * f₂ * u₁⁻¹) *
          ((u₁ * f₃ * u₁⁻¹) * (u₁ * f₄ * u₁⁻¹)) := by group
      _ = (f₂ * d₀) * (f₄ * f₃) := by rw [← hf₂, e2, e3, e4]
      _ = (d₀ * f₂) * (f₃ * f₄) := by rw [hc h₂ hd₀, hc h₄ h₃]
      _ = d₀ * f₂ * f₃ * f₄ := by group
  have hn₂ : u₂ * (d₀ * f₂ * f₃ * f₄) * u₂⁻¹ = d₀ * f₂ * f₃ * f₄ := by
    have e2 : u₂ * f₂ * u₂⁻¹ = f₄ := by rw [hf₂, hf₄, hu₁₂]; group
    have e3 : u₂ * f₃ * u₂⁻¹ = d₀ := by
      rw [hf₃, show u₂ * (u₂ * d₀ * u₂⁻¹) * u₂⁻¹ = (u₂ * u₂) * d₀ * (u₂ * u₂)⁻¹ by group,
        hu₂2]; group
    have e4 : u₂ * f₄ * u₂⁻¹ = f₂ := by
      rw [hf₄, hf₂, hu₁₂, show u₂ * ((u₂ * u₁) * d₀ * (u₂ * u₁)⁻¹) * u₂⁻¹ =
        (u₂ * u₂) * u₁ * d₀ * ((u₂ * u₂) * u₁)⁻¹ by group, hu₂2]; group
    calc u₂ * (d₀ * f₂ * f₃ * f₄) * u₂⁻¹ = ((u₂ * d₀ * u₂⁻¹) * (u₂ * f₂ * u₂⁻¹)) *
          ((u₂ * f₃ * u₂⁻¹) * (u₂ * f₄ * u₂⁻¹)) := by group
      _ = (f₃ * f₄) * (d₀ * f₂) := by rw [← hf₃, e2, e3, e4]
      _ = (d₀ * f₂) * (f₃ * f₄) := hc (mul_mem h₃ h₄) (mul_mem hd₀ h₂)
      _ = d₀ * f₂ * f₃ * f₄ := by group
  have hnX : d₀ * f₂ * f₃ * f₄ ∈ centralizer (d.X₁ : Set G) := by
    have hle : d.X₁ ≤ centralizer ({d₀ * f₂ * f₃ * f₄} : Set G) := by
      refine hX₁.trans ((closure_le _).mpr ?_)
      intro x hx
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      rcases hx with hx | hx
      · rw [hx]
        calc u₁ * (d₀ * f₂ * f₃ * f₄) = u₁ * (d₀ * f₂ * f₃ * f₄) * u₁⁻¹ * u₁ := by group
          _ = (d₀ * f₂ * f₃ * f₄) * u₁ := by rw [hn₁]
      · rw [Set.mem_singleton_iff.mp hx]
        calc u₂ * (d₀ * f₂ * f₃ * f₄) = u₂ * (d₀ * f₂ * f₃ * f₄) * u₂⁻¹ * u₂ := by group
          _ = (d₀ * f₂ * f₃ * f₄) * u₂ := by rw [hn₂]
    rw [mem_centralizer_iff]
    intro x hx
    exact mem_centralizer_singleton_iff.mp (hle hx)
  refine ⟨d₀ * f₂ * f₃ * f₄, mem_inf.mpr ⟨hnD, hnX⟩, ?_⟩
  have hU : ∀ {y}, y ∈ d.D₄ → y ∈ d.U₄ := fun hy => h.D_le_U₄ (h.D₄_le_D hy)
  have hcr : ∀ x ∈ d.X₁, (x * d₀ * x⁻¹)⁻¹ * d.t * (x * d₀ * x⁻¹) * d.t = x * a₀ * x⁻¹ := by
    intro x hx
    have hxt : x * d.t = d.t * x := h.comm_of_mem_L (h.Λ_le_L (h.X₁_le_Λ hx))
    rw [crossed_conj hxt, hd₀t, mul_assoc _ d.t d.t, h.t_sq, mul_one]
  have key : (d₀ * f₂ * f₃ * f₄)⁻¹ * d.t * (d₀ * f₂ * f₃ * f₄) * d.t = d.z := by
    rw [h.crossed_U₄_mul (hU (mul_mem (mul_mem hd₀ h₂) h₃)) (hU h₄),
      h.crossed_U₄_mul (hU (mul_mem hd₀ h₂)) (hU h₃), h.crossed_U₄_mul (hU hd₀) (hU h₂),
      hf₂, hf₃, hf₄, hcr u₁ hu₁, hcr u₂ hu₂, hcr _ (mul_mem hu₁ hu₂), hd₀t,
      mul_assoc a₀ d.t d.t, h.t_sq, mul_one, ← hnorm]
  rw [← key, mul_assoc _ d.t d.t, h.t_sq, mul_one]

theorem V₁_inf_H [Finite G] : d.V₁ ⊓ d.H = zpowers d.z := by
  refine le_antisymm h.V₁_inf_H_le ?_
  rw [zpowers_le]
  refine mem_inf.mpr ⟨h.z_mem_V₁, ?_⟩
  change d.z ∈ centralizer ({d.t} : Set G)
  rw [mem_centralizer_singleton_iff]
  exact h.z_comm_t

theorem card_V₁ [Finite G] : Nat.card d.V₁ = 4 := by
  have hVz : d.V₁ ≤ centralizer ((zpowers d.z : Subgroup G) : Set G) := by
    intro v hv
    rw [mem_centralizer_iff]
    intro g hg
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
    exact Commute.zpow_left (show Commute d.z v from h.V₁_comm h.z_mem_V₁ hv) k
  rw [card_eq_of_crossed_onto h.t_sq hVz (fun v hv => h.crossed_V₁ hv) ?_]
  · change Nat.card (d.V₁ ⊓ d.H : Subgroup G) * _ = _
    rw [h.V₁_inf_H, h.card_zpowers_z]
  · intro b hb
    rcases h.mem_zpowers_z_iff.mp hb with rfl | rfl
    · exact ⟨1, one_mem _, by rw [inv_one, one_mul, mul_one, h.t_sq]⟩
    · obtain ⟨v, hv, hvt⟩ := h.exists_V₁_conj
      exact ⟨v, hv, by rw [hvt, mul_assoc, h.t_sq, mul_one]⟩

theorem V₁_le_normalizer_ZR [Finite G] {v : G} (hv : v ∈ d.V₁) :
    v ∈ normalizer (d.ZR : Set G) := by
  apply mem_normalizer_of_conj_mem
  have hvz : v * d.z = d.z * v := h.V₁_comm hv h.z_mem_V₁
  have hle : d.ZR ≤ d.ZR.comap (MulAut.conj v).toMonoidHom := by
    refine sup_le ?_ ?_
    · rw [zpowers_le]
      change v * d.z * v⁻¹ ∈ d.ZR
      rw [hvz, mul_inv_cancel_right]
      exact mem_sup_left (mem_zpowers _)
    · rw [zpowers_le]
      change v * d.t * v⁻¹ ∈ d.ZR
      have hcr := h.crossed_V₁ (inv_mem hv)
      rw [inv_inv] at hcr
      have e : v * d.t * v⁻¹ = (v * d.t * v⁻¹ * d.t) * d.t := by
        rw [mul_assoc _ d.t d.t, h.t_sq, mul_one]
      rw [e]
      exact mul_mem (mem_sup_left hcr) (mem_sup_right (mem_zpowers _))
  exact fun y hy => hle hy

end Hyp

end CFSG.EvenSmallLie.UnitarySix.YamadaD
