module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDV1Sq
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaEndSection4
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDD1
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDD2

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaD

open Subgroup

structure Section4Out {G : Type} [Group G] (e : YamadaEnd.YamadaData G) : Prop where
  normalizer_center : normalizer (YamadaEnd.centerSub (e.S ⊔ zpowers e.t) : Set G) =
    (normalizer (e.A₁ : Set G) ⊓ e.H) ⊔ e.V₁
  V₁_normal : normalizer (YamadaEnd.centerSub (e.S ⊔ zpowers e.t) : Set G) ≤
    normalizer (e.V₁ : Set G)
  V₁_sq : ∀ v ∈ e.V₁, v * v = 1
  V₁_fix : e.V₁ ⊓ e.H ≤ e.S
  card_V₁ : Nat.card e.V₁ = 4
  K₁_centralizes : e.K₁ ≤ centralizer (e.V₁ : Set G)
  D₂_comm : ∀ x ∈ e.D₂, ∀ y ∈ e.D₂, x * y = y * x
  D₂_H : e.D₂ ⊓ e.H = e.A₂
  D₂_irred : ∀ E : Subgroup G, e.A₂ ≤ E → E ≤ e.D₂ → e.K₂ ≤ normalizer (E : Set G) →
    E = e.A₂ ∨ E = e.D₂
  V₁_le_D₂ : e.V₁ ≤ e.D₂
  D₁_H : e.D₁ ⊓ e.H = e.A₁
  card_D₁ : Nat.card e.D₁ = 2 ^ 18
  card_D₂ : Nat.card e.D₂ = 2 ^ 18

namespace Hyp

variable {G : Type} [Group G] {d : Data G} (h : Hyp d)
include h

theorem centerSub_eq (hSL : d.S ≤ d.L)
    (hZS : d.S ⊓ centralizer (d.S : Set G) = zpowers d.z) :
    YamadaEnd.centerSub (d.S ⊔ zpowers d.t) = d.ZR := by
  have hSt : ∀ b ∈ d.S, b * d.t = d.t * b := fun b hb => h.comm_of_mem_L (hSL hb)
  have htC : d.t ∈ centralizer ((d.S ⊔ zpowers d.t : Subgroup G) : Set G) := by
    refine mem_centralizer_sup (mem_centralizer_iff.mpr fun b hb => hSt b hb) ?_
    rw [mem_centralizer_iff]
    intro g hg
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
    exact (Commute.zpow_left (Commute.refl d.t) k)
  have hzZ : d.z ∈ d.S ⊓ centralizer (d.S : Set G) := hZS ▸ mem_zpowers _
  refine le_antisymm (fun x hx => ?_) (sup_le (zpowers_le.mpr ⟨mem_sup_left hzZ.1, ?_⟩)
    (zpowers_le.mpr ⟨mem_sup_right (mem_zpowers _), htC⟩))
  · obtain ⟨hxR, hxC⟩ := mem_inf.mp hx
    have hcS : ∀ {s : G}, s ∈ d.S → s ∈ centralizer ((d.S ⊔ zpowers d.t : Subgroup G) : Set G) →
        s ∈ zpowers d.z := fun hs hsC => hZS ▸ mem_inf.mpr ⟨hs,
          mem_centralizer_iff.mpr fun b hb => mem_centralizer_iff.mp hsC b (mem_sup_left hb)⟩
    rcases (mem_sup_zpowers_iff h.t_sq hSt).mp hxR with hxS | hxS
    · exact mem_sup_left (hcS hxS hxC)
    · have hz := hcS hxS (mul_mem hxC htC)
      have e : x = (x * d.t) * d.t := by rw [mul_assoc, h.t_sq, mul_one]
      rw [e]
      exact mul_mem (mem_sup_left hz) (mem_sup_right (mem_zpowers _))
  · exact mem_centralizer_sup hzZ.2 (by
      rw [mem_centralizer_iff]
      intro g hg
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
      exact (Commute.zpow_left (show Commute d.t d.z from h.z_comm_t.symm) k))

end Hyp

section Bridge

theorem section4Out {G : Type} [Group G] [Finite G] {d : Data G} (h : Hyp d) (hB : HypB d)
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (hSL : d.S ≤ d.L) (hZS : d.S ⊓ centralizer (d.S : Set G) = zpowers d.z)
    (e : YamadaEnd.YamadaData G) (eL : e.L = d.L) (et : e.t = d.t) (eS : e.S = d.S)
    (eA₁ : e.A₁ = d.A₁) (eA₂ : e.A₂ = d.A₂) (eK₁ : e.K₁ = d.K₁) (eK₂ : e.K₂ = d.K₂)
    (eV₁ : e.V₁ = d.V₁) (eD₁ : e.D₁ = d.D₁) (eD₂ : e.D₂ = d.D₂) : Section4Out e := by
  obtain ⟨L, t, S, A₁, A₂, K₁, K₂, X₁, X₂, X₃, J, V₁, D₁, D₂, N₁, N₂, P, w₁, w₂, w₃⟩ := e
  simp only at eL et eS eA₁ eA₂ eK₁ eK₂ eV₁ eD₁ eD₂
  subst eL et eS eA₁ eA₂ eK₁ eK₂ eV₁ eD₁ eD₂
  have hV : ∀ v ∈ d.V₁, v * v = 1 := fun v hv => h.V₁_sq hnonab hK hv
  have hzS : d.z ∈ d.S := (hZS ▸ mem_zpowers d.z : d.z ∈ d.S ⊓ _).1
  exact
    { normalizer_center := by
        rw [h.centerSub_eq hSL hZS]
        exact h.normalizer_ZR_eq
      V₁_normal := by
        rw [h.centerSub_eq hSL hZS]
        exact h.X_le_normalizer_V₁
      V₁_sq := hV
      V₁_fix := by
        change d.V₁ ⊓ d.H ≤ d.S
        rw [h.V₁_inf_H]
        exact zpowers_le.mpr hzS
      card_V₁ := h.card_V₁
      K₁_centralizes := h.K₁_le_cent_V₁
      D₂_comm := fun x hx y hy => h.D₂_comm hB hx hy
      D₂_H := h.D₂_inf_H
      D₂_irred := fun E hAE hED hKE => h.D₂_irred hB hAE hED hKE
      V₁_le_D₂ := h.V₁_le_D₂
      D₁_H := h.D₁_inf_H hB hV
      card_D₁ := h.card_D₁ hB hV
      card_D₂ := h.card_D₂ hB }

end Bridge

end CFSG.EvenSmallLie.UnitarySix.YamadaD
