module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.S3Cent

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

structure DData (V P D : Subgroup G) : Prop where
  le_V : D ≤ V
  eq : D = ⊥ ∨ D = V
  comm : ∀ a ∈ P, ∀ b ∈ P, ⁅a, b⁆ ∈ D
  card : 16 * Nat.card D ≤ Nat.card P

namespace Ctx3

variable {x : G} {T V H : Subgroup G} {f : G} {D : Subgroup G} (c : Ctx3 G x T V H f)
include c

theorem D_conj_T (hD : DData V (Hzero H f) D) {t : G} (ht : t ∈ T) :
    ∀ d ∈ D, t * d * t⁻¹ ∈ D := by
  rcases hD.eq with h | h
  · intro d hd
    rw [h] at hd
    have : d = 1 := (Subgroup.mem_bot).1 hd
    rw [this, h]
    simp
  · intro d hd
    rw [h] at hd ⊢
    exact c.out.V_norm t ht d hd

theorem T_norm_H0 [Finite G] (h9 : IG_9_16) (hD : DData V (Hzero H f) D) :
    ∀ t ∈ T, ∀ q ∈ Hzero H f, t * q * t⁻¹ ∈ Hzero H f := by
  intro t ht q hq
  by_contra hqt
  have hw : t * q * t⁻¹ ∈ H := by
    have := (mem_normalizer_iff.1 (c.T_norm_H ht) q).1 (c.H0_le hq)
    exact this
  have hle : cj t (Hzero H f) ≤ cenMod H D (t * q * t⁻¹) (c.D_norm hD.le_V) := by
    intro k hk
    have hk' : t⁻¹ * k * t ∈ Hzero H f := mem_cj.1 hk
    generalize ha : t⁻¹ * k * t = a at hk'
    have hka : k = t * a * t⁻¹ := by rw [← ha]; group
    have hkH : k ∈ H := by
      rw [hka]
      exact (mem_normalizer_iff.1 (c.T_norm_H ht) a).1 (c.H0_le hk')
    refine ⟨hkH, ?_⟩
    have e : (t * q * t⁻¹) * k * (t * q * t⁻¹)⁻¹ * k⁻¹ = t * ⁅q, a⁆ * t⁻¹ := by
      rw [hka]
      simp only [commutatorElement_def]
      group
    show (t * q * t⁻¹) * k * (t * q * t⁻¹)⁻¹ * k⁻¹ ∈ D
    rw [e]
    exact c.D_conj_T hD ht _ (hD.comm q hq a hk')
  have h1 := Subgroup.card_le_of_le hle
  rw [card_cj] at h1
  have h2 := (c.card_cenMod_w_le h9 hD.le_V hD.comm hw hqt).1
  have h3 := hD.card
  have hDpos : 0 < Nat.card D := Nat.card_pos
  omega

theorem Hstar_norm_H0 [Finite G] (h9 : IG_9_16) (hD : DData V (Hzero H f) D) :
    ∀ s ∈ H ⊔ T, ∀ q ∈ Hzero H f, s * q * s⁻¹ ∈ Hzero H f := by
  have hle : H ⊔ T ≤ normalizer ((Hzero H f : Subgroup G) : Set G) := by
    refine sup_le ?_ ?_
    · intro g hg
      rw [mem_normalizer_iff]
      intro q
      refine ⟨fun hq => c.H0_norm_H g hg q hq, fun hq => ?_⟩
      have := c.H0_norm_H g⁻¹ (H.inv_mem hg) _ hq
      have e : g⁻¹ * (g * q * g⁻¹) * g⁻¹⁻¹ = q := by group
      rwa [e] at this
    · intro t ht
      rw [mem_normalizer_iff]
      intro q
      refine ⟨fun hq => c.T_norm_H0 h9 hD t ht q hq, fun hq => ?_⟩
      have := c.T_norm_H0 h9 hD t⁻¹ (T.inv_mem ht) _ hq
      have e : t⁻¹ * (t * q * t⁻¹) * t⁻¹⁻¹ = q := by group
      rwa [e] at this
  intro s hs q hq
  exact (mem_normalizer_iff.1 (hle hs) q).1 hq

end Ctx3

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
