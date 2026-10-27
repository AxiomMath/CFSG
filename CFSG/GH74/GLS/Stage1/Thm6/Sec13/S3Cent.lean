module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.CenMod
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.S3Basic

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

namespace Ctx3

variable {x : G} {T V H : Subgroup G} {f : G} (c : Ctx3 G x T V H f)
include c

theorem H_cent_V {h v : G} (hh : h ∈ H) (hv : v ∈ V) : h * v * h⁻¹ = v := by
  have := mem_centralizer_iff.1 (c.H_C_V hh) v hv
  calc h * v * h⁻¹ = (v * h) * h⁻¹ := by rw [this]
    _ = v := by group

theorem D_norm {D : Subgroup G} (hDV : D ≤ V) : ∀ h ∈ H, ∀ n ∈ D, h * n * h⁻¹ ∈ D := by
  intro h hh n hn
  rw [c.H_cent_V hh (hDV hn)]
  exact hn

theorem P_relIndex_H [Finite G] : (Hzero H f).relIndex H = 2 := by
  have h1 := relIndex_mul_card (Hzero H f) H
  rw [inf_of_le_left c.H0_le, c.card_H] at h1
  have hpos : 0 < Nat.card (Hzero H f) := Nat.card_pos
  have : (Hzero H f).relIndex H * Nat.card (Hzero H f) = 2 * Nat.card (Hzero H f) := h1
  exact Nat.eq_of_mul_eq_mul_right hpos this

theorem cenMod_P_iff {D : Subgroup G} (hDV : D ≤ V)
    (hDP : ∀ a ∈ Hzero H f, ∀ b ∈ Hzero H f, ⁅a, b⁆ ∈ D) {q : G} (hq : q ∈ Hzero H f) {g : G}
    (hg : g ∈ Hzero H f) :
    (q * x) * g * (q * x)⁻¹ * g⁻¹ ∈ D ↔ x * g * x⁻¹ * g⁻¹ ∈ D := by
  have hqH : q ∈ H := c.H0_le hq
  have e : (q * x) * g * (q * x)⁻¹ * g⁻¹ =
      (q * (x * g * x⁻¹ * g⁻¹) * q⁻¹) * ⁅q, g⁆ := by
    simp only [commutatorElement_def]; group
  have hc1 : ⁅q, g⁆ ∈ D := hDP q hq g hg
  rw [e]
  constructor
  · intro h
    have h1 : q * (x * g * x⁻¹ * g⁻¹) * q⁻¹ ∈ D := by
      have e' : q * (x * g * x⁻¹ * g⁻¹) * q⁻¹ =
          (q * (x * g * x⁻¹ * g⁻¹) * q⁻¹ * ⁅q, g⁆) * (⁅q, g⁆)⁻¹ := by group
      rw [e']
      exact D.mul_mem h (D.inv_mem hc1)
    have h2 := c.D_norm hDV q⁻¹ (H.inv_mem hqH) _ h1
    have e2 : q⁻¹ * (q * (x * g * x⁻¹ * g⁻¹) * q⁻¹) * q⁻¹⁻¹ = x * g * x⁻¹ * g⁻¹ := by group
    rw [e2] at h2
    exact h2
  · intro h
    exact D.mul_mem (c.D_norm hDV q hqH _ h) hc1

theorem card_cenMod_x_le [Finite G] (h9 : IG_9_16) {D : Subgroup G} (hDV : D ≤ V) :
    Nat.card (cenMod H D x (c.D_norm hDV)) ≤ 8 * Nat.card D := by
  have hDH : D ≤ H := fun d hd => c.H0_le (c.V_le_H0 (hDV hd))
  have h := card_cenMod_le h9 hDH (c.D_norm hDV) c.x_mem_H
  rw [InH.C_H_x c.out c.hI, c.out.card_EV] at h
  calc Nat.card (cenMod H D x (c.D_norm hDV)) ≤ Nat.card D * 8 := h
    _ = 8 * Nat.card D := by ring

theorem card_cenMod_w_le [Finite G] (h9 : IG_9_16) {D : Subgroup G} (hDV : D ≤ V)
    (hDP : ∀ a ∈ Hzero H f, ∀ b ∈ Hzero H f, ⁅a, b⁆ ∈ D) {w : G} (hw : w ∈ H)
    (hwP : w ∉ Hzero H f) :
    Nat.card (cenMod H D w (c.D_norm hDV)) ≤ 8 * Nat.card D ∧
      Nat.card ↥(Hzero H f ⊓ cenMod H D w (c.D_norm hDV)) ≤ 4 * Nat.card D := by
  obtain ⟨q, hq, hwq | hwq⟩ := (c.mem_H_iff).1 hw
  · exact absurd (hwq ▸ hq) hwP
  have hP2 := c.P_relIndex_H
  have hHne : (Hzero H f).relIndex H ≠ 0 := by rw [hP2]; norm_num
  have hPK : Hzero H f ⊓ cenMod H D w (c.D_norm hDV) = Hzero H f ⊓ cenMod H D x (c.D_norm hDV) := by
    ext g
    constructor
    · rintro ⟨hgP, hgK⟩
      refine ⟨hgP, ?_, ?_⟩
      · exact c.H0_le hgP
      · have := hgK.2
        rw [hwq] at this
        exact (c.cenMod_P_iff hDV hDP hq hgP).1 this
    · rintro ⟨hgP, hgK⟩
      refine ⟨hgP, c.H0_le hgP, ?_⟩
      rw [hwq]
      exact (c.cenMod_P_iff hDV hDP hq hgP).2 hgK.2
  have hKx := c.card_cenMod_x_le h9 hDV
  have hxK : x ∈ cenMod H D x (c.D_norm hDV) := by
    refine ⟨c.x_mem_H, ?_⟩
    have e : x * x * x⁻¹ * x⁻¹ = 1 := by group
    rw [e]
    exact D.one_mem
  have hrx : (Hzero H f).relIndex (cenMod H D x (c.D_norm hDV)) = 2 := by
    have hle : (Hzero H f).relIndex (cenMod H D x (c.D_norm hDV)) ≤ 2 := by
      rw [← hP2]
      exact relIndex_le_of_le_right (fun g hg => hg.1) hHne
    have hne1 : (Hzero H f).relIndex (cenMod H D x (c.D_norm hDV)) ≠ 1 := by
      intro h1
      rw [relIndex_eq_one] at h1
      exact c.x_notin_H0 (h1 hxK)
    have hpos : 0 < (Hzero H f).relIndex (cenMod H D x (c.D_norm hDV)) := by
      rcases Nat.eq_zero_or_pos ((Hzero H f).relIndex (cenMod H D x (c.D_norm hDV))) with h0 | h0
      · exfalso
        have hm := relIndex_mul_card (Hzero H f) (cenMod H D x (c.D_norm hDV))
        rw [h0, zero_mul] at hm
        have : 0 < Nat.card (cenMod H D x (c.D_norm hDV)) := Nat.card_pos
        omega
      · exact h0
    omega
  have hmx := relIndex_mul_card (Hzero H f) (cenMod H D x (c.D_norm hDV))
  rw [hrx] at hmx
  have hmw := relIndex_mul_card (Hzero H f) (cenMod H D w (c.D_norm hDV))
  have hrw : (Hzero H f).relIndex (cenMod H D w (c.D_norm hDV)) ≤ 2 := by
    rw [← hP2]
    exact relIndex_le_of_le_right (fun g hg => hg.1) hHne
  rw [hPK] at hmw ⊢
  have hP4 : Nat.card ↥(Hzero H f ⊓ cenMod H D x (c.D_norm hDV)) ≤ 4 * Nat.card D := by omega
  refine ⟨?_, hP4⟩
  calc Nat.card (cenMod H D w (c.D_norm hDV))
      = (Hzero H f).relIndex (cenMod H D w (c.D_norm hDV)) *
        Nat.card ↥(Hzero H f ⊓ cenMod H D x (c.D_norm hDV)) := hmw.symm
    _ ≤ 2 * Nat.card ↥(Hzero H f ⊓ cenMod H D x (c.D_norm hDV)) := Nat.mul_le_mul_right _ hrw
    _ ≤ 8 * Nat.card D := by omega

end Ctx3

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
