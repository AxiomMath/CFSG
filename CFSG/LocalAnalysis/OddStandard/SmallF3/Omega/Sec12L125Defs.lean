module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

structure Sec125Core (t : G) (V E : Subgroup G) : Prop where
  comm : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v
  sq : ∀ v ∈ V, v * v = 1
  tsq : t * t = 1
  tnorm : ∀ v ∈ V, t * v * t⁻¹ ∈ V
  sup : V ⊔ zpowers t = E
  nofix : ∃ v ∈ V, t * v ≠ v * t
  trans : ∀ v ∈ V, v * t = t * v → ∃ w ∈ V, w * t * w⁻¹ = v * t
  two : ∀ c ∈ centralizer (E : Set G), (∃ k : ℕ, c ^ (2 ^ k) = 1) → c ∈ V

namespace Sec125Core

variable {t : G} {V E : Subgroup G}

theorem inv_eq (h : Sec125Core t V E) {v : G} (hv : v ∈ V) : v⁻¹ = v :=
  inv_eq_of_mul_eq_one_right (h.sq v hv)

theorem t_not_mem (h : Sec125Core t V E) : t ∉ V := by
  intro ht
  obtain ⟨v, hv, hne⟩ := h.nofix
  exact hne (h.comm t ht v hv)

theorem t_ne_one (h : Sec125Core t V E) : t ≠ 1 := fun h1 => h.t_not_mem (h1 ▸ V.one_mem)

theorem t_mem_normalizer (h : Sec125Core t V E) : t ∈ normalizer (V : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro v
  refine ⟨h.tnorm v, fun hv => ?_⟩
  have h1 := h.tnorm _ hv
  have h2 : t * (t * v * t⁻¹) * t⁻¹ = v := by
    calc t * (t * v * t⁻¹) * t⁻¹ = (t * t) * v * (t⁻¹ * t⁻¹) := by group
      _ = v := by rw [h.tsq, ← mul_inv_rev, h.tsq]; group
  rwa [h2] at h1

theorem zpowers_le_normalizer (h : Sec125Core t V E) : zpowers t ≤ normalizer (V : Set G) :=
  (Subgroup.zpowers_le).2 h.t_mem_normalizer

theorem mem_zpowers (h : Sec125Core t V E) {c : G} (hc : c ∈ zpowers t) : c = 1 ∨ c = t := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  have ho : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact h.tsq) h.t_ne_one
  rw [← zpow_mod_orderOf, ho]
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    simp [h0]
  · right
    simp [h1]

theorem t_mem (h : Sec125Core t V E) : t ∈ E :=
  h.sup ▸ (le_sup_right : zpowers t ≤ V ⊔ zpowers t) (Subgroup.mem_zpowers t)

theorem V_le (h : Sec125Core t V E) : V ≤ E := h.sup ▸ le_sup_left

theorem mem_E (h : Sec125Core t V E) {x : G} : x ∈ E ↔ x ∈ V ∨ ∃ v ∈ V, x = v * t := by
  constructor
  · intro hx
    rw [← h.sup, ← SetLike.mem_coe,
      Subgroup.coe_mul_of_right_le_normalizer_left V (zpowers t) h.zpowers_le_normalizer] at hx
    obtain ⟨v, hv, c, hc, rfl⟩ := hx
    rcases h.mem_zpowers hc with rfl | rfl
    · exact Or.inl (by simpa using hv)
    · exact Or.inr ⟨v, hv, rfl⟩
  · rintro (hx | ⟨v, hv, rfl⟩)
    · exact h.V_le hx
    · exact E.mul_mem (h.V_le hv) h.t_mem

theorem comm_of_sq (h : Sec125Core t V E) {v : G} (hv : v ∈ V) (hsq : v * t * (v * t) = 1) :
    v * t = t * v := by
  have h1 : t * v * t = v := by
    have h2 : v⁻¹ * (v * t * (v * t)) = t * v * t := by group
    rw [hsq, mul_one, h.inv_eq hv] at h2
    exact h2.symm
  calc v * t = (t * v * t) * t := by rw [h1]
    _ = t * v := by rw [mul_assoc, h.tsq, mul_one]

theorem mem_V_of_centralizes (h : Sec125Core t V E) {e : G} (he : e ∈ E)
    (hc : ∀ v ∈ V, e * v = v * e) : e ∈ V := by
  rcases h.mem_E.mp he with hV | ⟨v₀, hv₀, rfl⟩
  · exact hV
  · exfalso
    obtain ⟨v, hv, hne⟩ := h.nofix
    apply hne
    have h1 : v₀ * (t * v) = v₀ * (v * t) := by
      calc v₀ * (t * v) = v₀ * t * v := by rw [mul_assoc]
        _ = v * (v₀ * t) := hc v hv
        _ = (v * v₀) * t := by rw [mul_assoc]
        _ = (v₀ * v) * t := by rw [h.comm v hv v₀ hv₀]
        _ = v₀ * (v * t) := by rw [mul_assoc]
    exact mul_left_cancel h1

theorem exists_comm (h : Sec125Core t V E) {x : G} (hxE : x * t * x⁻¹ ∈ E)
    (hxV : x ∈ normalizer (V : Set G)) : ∃ w ∈ V, (w⁻¹ * x) * t = t * (w⁻¹ * x) := by
  rcases h.mem_E.mp hxE with hV | ⟨v, hv, hvt⟩
  · exact absurd ((Subgroup.mem_normalizer_iff.mp hxV t).mpr hV) h.t_not_mem
  · have hsq : (v * t) * (v * t) = 1 := by
      rw [← hvt]
      calc x * t * x⁻¹ * (x * t * x⁻¹) = x * (t * t) * x⁻¹ := by group
        _ = 1 := by rw [h.tsq]; group
    obtain ⟨w, hw, hwt⟩ := h.trans v hv (h.comm_of_sq hv hsq)
    refine ⟨w, hw, ?_⟩
    calc w⁻¹ * x * t = w⁻¹ * (x * t * x⁻¹) * x := by group
      _ = w⁻¹ * (w * t * w⁻¹) * x := by rw [hvt, ← hwt]
      _ = t * (w⁻¹ * x) := by group

end Sec125Core

end CFSG.OddStandard.SmallF3.Omega
