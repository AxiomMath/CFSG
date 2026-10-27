module

public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

public section

namespace CFSG.ComponentClassification.FooteLit.AltCore

open Equiv Equiv.Perm

theorem not_odd_orderOf_of_mul_self {G : Type*} [Group G] {y : G} (h : y * y = 1)
    (h1 : y ≠ 1) : ¬ Odd (orderOf y) := by
  rw [orderOf_eq_prime (by rw [sq]; exact h) h1]
  decide

variable {α : Type*} [DecidableEq α]

theorem not_odd_orderOf_swap_mul_swap {p q r s : α} (hpq : p ≠ q) (_hrs : r ≠ s) (hpr : p ≠ r)
    (hps : p ≠ s) (hqr : q ≠ r) (hqs : q ≠ s) : ¬ Odd (orderOf (swap p q * swap r s)) := by
  have hd : Perm.Disjoint (swap p q) (swap r s) := by
    intro x
    by_cases hx : x = p ∨ x = q
    · right
      rcases hx with rfl | rfl
      · exact swap_apply_of_ne_of_ne hpr hps
      · exact swap_apply_of_ne_of_ne hqr hqs
    · left
      push Not at hx
      exact swap_apply_of_ne_of_ne hx.1 hx.2
  have hc : swap p q * swap r s = swap r s * swap p q := hd.commute.eq
  apply not_odd_orderOf_of_mul_self
  · rw [mul_assoc, ← mul_assoc (swap r s) (swap p q), ← hc, mul_assoc, swap_mul_self, mul_one,
      swap_mul_self]
  · intro h
    have h1 := congrArg (fun σ : Perm α => σ p) h
    simp only [Perm.mul_apply, swap_apply_of_ne_of_ne hpr hps, swap_apply_left,
      Perm.one_apply] at h1
    exact hpq h1.symm

omit [DecidableEq α] in
theorem apply_eq_of_odd_of_apply_apply {x : Perm α} (hx : Odd (orderOf x)) {a : α}
    (h : x (x a) = a) : x a = a := by
  obtain ⟨k, hk⟩ := hx
  have h1 : ∀ j : ℕ, (x ^ (2 * j)) a = a := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [show 2 * (j + 1) = 2 * j + 2 by ring, pow_add, Perm.mul_apply, sq, Perm.mul_apply, h,
        ih]
  have h2 : x ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one x
  calc x a = (x ^ (2 * k + 1)) a := by rw [pow_succ', Perm.mul_apply, h1 k]
    _ = a := by rw [h2, Perm.one_apply]

variable {π : Perm α} {O : Subgroup (Perm α)}

theorem swap_mul_eq_of_apply {a b : α} (h : swap (π a) (π b) = swap a b) :
    swap a b * π = π * swap a b := by
  have h1 : π * swap a b * π⁻¹ = swap a b := by rw [← swap_apply_apply, h]
  calc swap a b * π = π * swap a b * π⁻¹ * π := by rw [h1]
    _ = π * swap a b := by group

omit [DecidableEq α] in
theorem commutator_mem
    (hnorm : ∀ g : Perm α, g * π = π * g → ∀ x ∈ O, g * x * g⁻¹ ∈ O) {x g : Perm α}
    (hx : x ∈ O) (hg : g * π = π * g) : x * g * x⁻¹ * g⁻¹ ∈ O := by
  have h1 := hnorm g hg x⁻¹ (inv_mem hx)
  rw [show x * g * x⁻¹ * g⁻¹ = x * (g * x⁻¹ * g⁻¹) by group]
  exact mul_mem hx h1

variable (hπ : π * π = 1) (hO : ∀ x ∈ O, x * π = π * x) (hodd : ∀ x ∈ O, Odd (orderOf x))
  (hnorm : ∀ g : Perm α, g * π = π * g → ∀ x ∈ O, g * x * g⁻¹ ∈ O)
include hπ hO hodd hnorm

theorem apply_eq_of_moved {x : Perm α} (hx : x ∈ O) {a : α} (ha : π a ≠ a) : x a = a := by
  have hπa : π (π a) = a := by rw [← Perm.mul_apply, hπ, Perm.one_apply]
  have hτ : swap a (π a) * π = π * swap a (π a) :=
    swap_mul_eq_of_apply (by rw [hπa, swap_comm])
  have hy := commutator_mem hnorm hx hτ
  rw [← swap_apply_apply, swap_inv] at hy
  have hxπ : x (π a) = π (x a) := by rw [← Perm.mul_apply, hO x hx, Perm.mul_apply]
  have hxa : x a = a ∨ x a = π a := by
    by_contra h
    push Not at h
    obtain ⟨h1, h2⟩ := h
    have h3 : x (π a) ≠ a := by
      rw [hxπ]
      intro h
      apply h2
      have e : π (π (x a)) = x a := by rw [← Perm.mul_apply, hπ, Perm.one_apply]
      rw [h] at e
      exact e.symm
    have h4 : x (π a) ≠ π a := by
      rw [hxπ]
      intro h
      exact h1 (π.injective h)
    have h5 : x a ≠ x (π a) := fun h => ha (x.injective h).symm
    exact not_odd_orderOf_swap_mul_swap h5 (Ne.symm ha) h1 h2 h3 h4 (hodd _ hy)
  rcases hxa with h | h
  · exact h
  · exfalso
    have h6 : x (x a) = a := by rw [h, hxπ, h, hπa]
    exact ha (h.symm.trans (apply_eq_of_odd_of_apply_apply (hodd x hx) h6))

omit hπ in
theorem apply_eq_of_fixed {x : Perm α} (hx : x ∈ O) {c d : α} (hc : π c = c) (hxc : x c ≠ c)
    (hd : π d = d) (hdc : d ≠ c) (hdc' : d ≠ x c) (hdc'' : d ≠ x (x c)) : x d = d := by
  have hπxc : π (x c) = x c := by rw [← Perm.mul_apply, ← hO x hx, Perm.mul_apply, hc]
  have hσ : swap (x c) d * π = π * swap (x c) d := swap_mul_eq_of_apply (by rw [hπxc, hd])
  have hy := commutator_mem hnorm hx hσ
  rw [← swap_apply_apply, swap_inv] at hy
  by_contra hxd
  have h1 : x (x c) ≠ x d := fun h => hdc' (x.injective h).symm
  have h3 : x (x c) ≠ x c := fun h => hxc (x.injective h)
  have h5 : x d ≠ x c := fun h => hdc (x.injective h)
  exact not_odd_orderOf_swap_mul_swap h1 (Ne.symm hdc') h3 (Ne.symm hdc'') h5 hxd (hodd _ hy)

omit hπ in
theorem apply_apply_apply {x : Perm α} (hx : x ∈ O) {c : α} (hc : π c = c) (hxc : x c ≠ c) :
    x (x (x c)) = c := by
  have hfix : ∀ p, π p = p → π (x p) = x p := fun p hp => by
    rw [← Perm.mul_apply, ← hO x hx, Perm.mul_apply, hp]
  have hc₂ : x (x c) ≠ c := fun h => hxc (apply_eq_of_odd_of_apply_apply (hodd x hx) h)
  have hc₁₂ : x c ≠ x (x c) := fun h => hxc (x.injective h).symm
  by_contra hne
  have he1 : x (x (x c)) ≠ x c := fun h => hc₂ (x.injective h)
  have he2 : x (x (x c)) ≠ x (x c) := fun h => hc₁₂ (x.injective h).symm
  have := apply_eq_of_fixed hO hodd hnorm hx hc hxc (hfix _ (hfix _ (hfix _ hc))) hne he1 he2
  exact he2 (x.injective this)

theorem mem_of_fixed {x : Perm α} (hx : x ∈ O) {c : α} (hc : π c = c) (hxc : x c ≠ c) {d : α}
    (hd : π d = d) : d = c ∨ d = x c ∨ d = x (x c) := by
  by_contra h
  push Not at h
  obtain ⟨hdc, hdc', hdc''⟩ := h
  have hfix : ∀ p, π p = p → π (x p) = x p := fun p hp => by
    rw [← Perm.mul_apply, ← hO x hx, Perm.mul_apply, hp]
  have hc₂ : x (x c) ≠ c := fun h => hxc (apply_eq_of_odd_of_apply_apply (hodd x hx) h)
  have hc₁₂ : x c ≠ x (x c) := fun h => hxc (x.injective h).symm
  have h3 := apply_apply_apply hO hodd hnorm hx hc hxc
  have hxd := apply_eq_of_fixed hO hodd hnorm hx hc hxc hd hdc hdc' hdc''
  have hrest : ∀ p, p ≠ c → p ≠ x c → p ≠ x (x c) → x p = p := fun p h1 h2 h3 => by
    by_cases hp : π p = p
    · exact apply_eq_of_fixed hO hodd hnorm hx hc hxc hp h1 h2 h3
    · exact apply_eq_of_moved hπ hO hodd hnorm hx hp
  set σ := swap (x (x c)) d with hσdef
  have hσ : σ * π = π * σ := swap_mul_eq_of_apply (by rw [hfix _ (hfix _ hc), hd])
  have hz : x * (σ * x * σ⁻¹) ∈ O := mul_mem hx (hnorm σ hσ x hx)
  have hzeq : x * (σ * x * σ⁻¹) = swap c (x (x c)) * swap (x c) d := by
    have e1 : c ≠ x c := Ne.symm hxc
    have e2 : c ≠ x (x c) := Ne.symm hc₂
    have e3 : c ≠ d := Ne.symm hdc
    have e5 : x c ≠ d := Ne.symm hdc'
    have e6 : x (x c) ≠ d := Ne.symm hdc''
    rw [hσdef, swap_inv]
    refine Equiv.ext fun p => ?_
    simp only [Perm.mul_apply]
    by_cases hp1 : p = c
    · subst hp1
      simp [swap_apply_def, e1, e2, e3, hc₁₂, e5]
    by_cases hp2 : p = x c
    · subst hp2
      simp [swap_apply_def, hc₁₂, e5, e3.symm, e6.symm, hxd]
    by_cases hp3 : p = x (x c)
    · subst hp3
      simp [swap_apply_def, e6, hc₁₂.symm, hxd, h3]
    by_cases hp4 : p = d
    · subst hp4
      simp [swap_apply_def, e2, e3, hc₁₂, e1.symm, h3]
    · have hxp := hrest p hp1 hp2 hp3
      simp [swap_apply_def, hp1, hp2, hp3, hp4, hxp]
  rw [hzeq] at hz
  exact not_odd_orderOf_swap_mul_swap hc₂.symm hdc'.symm (Ne.symm hxc) hdc.symm
    hc₁₂.symm hdc''.symm (hodd _ hz)

theorem apply_ne_of_fixed {z : Perm α} (hz : z ∈ O) (hz1 : z ≠ 1) {p : α} (hp : π p = p) :
    z p ≠ p := by
  obtain ⟨q, hq⟩ : ∃ q, z q ≠ q := by
    by_contra h
    push Not at h
    exact hz1 (Equiv.ext h)
  have hπq : π q = q := by
    by_contra h
    exact hq (apply_eq_of_moved hπ hO hodd hnorm hz h)
  have h3 := apply_apply_apply hO hodd hnorm hz hπq hq
  have hc₂ : z (z q) ≠ q := fun h => hq (apply_eq_of_odd_of_apply_apply (hodd z hz) h)
  have hc₁₂ : z q ≠ z (z q) := fun h => hq (z.injective h).symm
  rcases mem_of_fixed hπ hO hodd hnorm hz hπq hq hp with rfl | rfl | rfl
  · exact hq
  · exact hc₁₂.symm
  · rw [h3]
    exact hc₂.symm

theorem commute_of_mem {x y : Perm α} (hx : x ∈ O) (hy : y ∈ O) : x * y = y * x := by
  by_cases hx1 : x = 1
  · rw [hx1, one_mul, mul_one]
  obtain ⟨c, hxc⟩ : ∃ c, x c ≠ c := by
    by_contra h
    push Not at h
    exact hx1 (Equiv.ext h)
  have hc : π c = c := by
    by_contra h
    exact hxc (apply_eq_of_moved hπ hO hodd hnorm hx h)
  have hfix : ∀ p, π p = p → π (y p) = y p := fun p hp => by
    rw [← Perm.mul_apply, ← hO y hy, Perm.mul_apply, hp]
  have h3 := apply_apply_apply hO hodd hnorm hx hc hxc
  rcases mem_of_fixed hπ hO hodd hnorm hx hc hxc (hfix c hc) with h | h | h
  ·
    by_cases hy1 : y = 1
    · rw [hy1, one_mul, mul_one]
    exact absurd h (apply_ne_of_fixed hπ hO hodd hnorm hy hy1 hc)
  ·
    have hz : y * x⁻¹ ∈ O := mul_mem hy (inv_mem hx)
    have hzfix : (y * x⁻¹) (x c) = x c := by
      rw [Perm.mul_apply, ← Perm.mul_apply x⁻¹, inv_mul_cancel, Perm.one_apply, h]
    have hπxc : π (x c) = x c := by rw [← Perm.mul_apply, ← hO x hx, Perm.mul_apply, hc]
    by_cases hz1 : y * x⁻¹ = 1
    · rw [mul_inv_eq_one.mp hz1]
    · exact absurd hzfix (apply_ne_of_fixed hπ hO hodd hnorm hz hz1 hπxc)
  ·
    have hz : y * x ∈ O := mul_mem hy hx
    have hzfix : (y * x) (x (x c)) = x (x c) := by
      rw [Perm.mul_apply, h3, h]
    have hfixx : ∀ p, π p = p → π (x p) = x p := fun p hp => by
      rw [← Perm.mul_apply, ← hO x hx, Perm.mul_apply, hp]
    have hπxxc : π (x (x c)) = x (x c) := hfixx _ (hfixx _ hc)
    by_cases hz1 : y * x = 1
    · rw [mul_eq_one_iff_eq_inv.mp hz1, mul_inv_cancel, inv_mul_cancel]
    · exact absurd hzfix (apply_ne_of_fixed hπ hO hodd hnorm hz hz1 hπxxc)

end CFSG.ComponentClassification.FooteLit.AltCore
