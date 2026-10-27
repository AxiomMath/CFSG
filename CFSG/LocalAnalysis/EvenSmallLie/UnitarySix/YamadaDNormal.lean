module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDD1Elem

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaD

open Subgroup

variable {G : Type*} [Group G]

namespace Hyp

variable {d : Data G} (h : Hyp d) (hB : HypB d)
include h hB

theorem C₂_eq_D₂_t [Finite G] : d.C₂ = d.D₂ ⊔ zpowers d.t := by
  have htC : d.t ∈ d.C₂ := by
    have := t_mem_withT (d := d) d.A₂
    rw [← h.C₂_inf_H] at this
    exact this.1
  have hle : d.D₂ ⊔ zpowers d.t ≤ d.C₂ := sup_le inf_le_left (zpowers_le.mpr htC)
  refine (eq_of_le_of_card_ge hle ?_).symm
  have hlt : d.D₂ < d.D₂ ⊔ zpowers d.t := lt_of_le_of_ne le_sup_left fun e => by
    have : d.t ∈ d.D₂ := e ▸ mem_sup_right (mem_zpowers _)
    exact h.t_not_cent_V₁ this.2
  have hdvd := card_dvd_of_le (le_sup_left : d.D₂ ≤ d.D₂ ⊔ zpowers d.t)
  have hne : Nat.card d.D₂ ≠ Nat.card (d.D₂ ⊔ zpowers d.t : Subgroup G) := fun e =>
    hlt.ne (eq_of_le_of_card_ge le_sup_left e.ge)
  obtain ⟨k, hk⟩ := hdvd
  rw [h.card_C₂, hk, h.card_D₂ hB]
  rw [hk, h.card_D₂ hB] at hne
  have hk0 : k ≠ 0 := fun e => by
    rw [e, mul_zero] at hk
    exact (Nat.card_pos (α := (d.D₂ ⊔ zpowers d.t : Subgroup G))).ne' hk
  have hk1 : k ≠ 1 := fun e => hne (by rw [e, mul_one])
  have : 2 ≤ k := by omega
  calc 2 ^ 19 = 2 ^ 18 * 2 := by norm_num
    _ ≤ 2 ^ 18 * k := Nat.mul_le_mul_left _ this

theorem theta_mem_V₁_iff [Finite G] (hV : ∀ v ∈ d.V₁, v * v = 1) {x : G} (hx : x ∈ d.D₁) :
    d.theta x ∈ d.V₁ ↔ x ∈ d.AV := by
  constructor
  · intro hθ
    rw [← h.D₁_inf_C₀ hB hV]
    exact mem_inf.mpr ⟨hx, h.mem_C₀_of_theta hB hV (h.D₁_le_U₁ hB hV hx) hθ⟩
  · intro hxA
    exact h.theta_mem_V₁_of_C₀ (h.AV_le_C₀ hxA)

end Hyp

end CFSG.EvenSmallLie.UnitarySix.YamadaD
