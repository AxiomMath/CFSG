module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.DCtx

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

namespace D13

variable {x : G} {T V H : Subgroup G} {f : G} (d : D13 x T V H f)
include d

theorem fixed_H0_trivial [Finite G] (hinv : ∀ q ∈ Hzero H f, q * q = 1 → q ∈ V) {f' : G}
    (hf'3 : Is3Element f') (hf'V : f' ∈ normalizer (V : Set G))
    (hnc : ∃ v ∈ V, f' * v * f'⁻¹ ≠ v) {q : G} (hq : q ∈ Hzero H f)
    (hfq : f' * q * f'⁻¹ = q) : q = 1 := by
  by_contra hq1
  have hqH : q ∈ H := d.H0_le hq
  obtain ⟨s, hs⟩ := d.hI.H2.exists_orderOf_eq_pow (⟨q, hqH⟩ : ↥H)
  rw [Subgroup.orderOf_mk] at hs
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, pow_zero, orderOf_eq_one_iff] at hs
    exact hq1 hs
  set u₀ := q ^ 2 ^ (s - 1) with hu₀
  have hu₀H0 : u₀ ∈ Hzero H f := pow_mem hq _
  have hu₀sq : u₀ * u₀ = 1 := by
    rw [hu₀, ← pow_add, ← two_mul, ← pow_succ']
    have : s - 1 + 1 = s := by omega
    rw [this, ← hs]
    exact pow_orderOf_eq_one q
  have hu₀V : u₀ ∈ V := hinv u₀ hu₀H0 hu₀sq
  have hu₀fix : f' * u₀ * f'⁻¹ = u₀ := by
    rw [hu₀, ← conj_pow, hfq]
  obtain ⟨k, hk⟩ := hf'3
  have hN : ∀ v ∈ V, f' * v * f'⁻¹ ∈ V := fun v hv => (mem_normalizer_iff.1 hf'V v).1 hv
  have h1 := fix_free_four V f' k hk hN d.out.V_four.2 hnc u₀ hu₀V hu₀fix
  apply hq1
  have hdvd : orderOf q ∣ 2 ^ (s - 1) := by
    rw [orderOf_dvd_iff_pow_eq_one]
    rw [hu₀] at h1
    exact h1
  rw [hs] at hdvd
  have : 2 ^ s ≤ 2 ^ (s - 1) := Nat.le_of_dvd (by positivity) hdvd
  have h2 : 2 ^ (s - 1) < 2 ^ s := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

theorem cent_H_f' [Finite G] (hinv : ∀ q ∈ Hzero H f, q * q = 1 → q ∈ V) {f' : G}
    (hf'3 : Is3Element f') (hf'V : f' ∈ normalizer (V : Set G)) (hf'x : f' * x = x * f')
    (hnc : ∃ v ∈ V, f' * v * f'⁻¹ ≠ v) {u : G} (hu : u ∈ H) (hfu : f' * u * f'⁻¹ = u) :
    u = 1 ∨ u = x := by
  rw [← d.iv2] at hu
  obtain ⟨q, hq, hu' | hu'⟩ := (mem_sup_zpowers_invol d.out.x_sq (fun q hq => d.iv3 x d.hI.x_mem q hq)).1 hu
  · left
    rw [hu'] at hfu ⊢
    exact d.fixed_H0_trivial hinv hf'3 hf'V hnc hq hfu
  · right
    rw [hu'] at hfu ⊢
    have hfx : f' * x * f'⁻¹ = x := mul_inv_eq_iff_eq_mul.2 hf'x
    have h1 : f' * q * f'⁻¹ = q := by
      have e : f' * (q * x) * f'⁻¹ = (f' * q * f'⁻¹) * (f' * x * f'⁻¹) := by group
      rw [e, hfx] at hfu
      exact mul_right_cancel hfu
    have := d.fixed_H0_trivial hinv hf'3 hf'V hnc hq h1
    rw [this, one_mul]

end D13

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
