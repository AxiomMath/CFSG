module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneFinkelsteinBasic

public section

namespace CFSG.SeitzReduction.RankOne.Finkelstein

open CFSG.ComponentClassification.GMS78.Finkelstein

variable {U : Type} [Group U] {n : ℕ} {t y : MulAut U}

theorem map_pow_of_comm {f : U → U} (hf : ∀ u, f (y u) = y (f u)) (k : ℕ) (u : U) :
    f ((y ^ k) u) = (y ^ k) (f u) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply, hf, ih, MulAut.mul_apply]

theorem pow_pow_apply_comm (s : MulAut U) (i k : ℕ) (u : U) :
    (s ^ i) ((s ^ k) u) = (s ^ k) ((s ^ i) u) := by
  rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← pow_add, ← pow_add, add_comm]

namespace Hyp

variable (h : Hyp U n t y)
include h

theorem eq_one_of_y_fix {a : U} (ha : a ∈ fixSubgroup t) (hya : y a = a) : a = 1 := by
  by_contra ha1
  have h1 := h.pow_eq_one_of_fix (k := 1) ha ha1 (by rw [pow_one]; exact hya)
  have h2 := h.order
  rw [pow_one] at h1
  rw [h1, orderOf_one] at h2
  have := h.three_le
  omega

theorem y_pow_sub_one : y ^ (2 ^ n - 1) = 1 := by
  rw [← h.order]
  exact pow_orderOf_eq_one y

theorem y_pow_two_pow : y ^ (2 ^ n) = y := by
  have h1 : 2 ^ n = (2 ^ n - 1) + 1 := by
    have := Nat.one_le_two_pow (n := n)
    omega
  rw [h1, pow_succ, h.y_pow_sub_one, one_mul]

theorem exists_pow_eq_pow_mul_sq (a b : ℕ) : ∃ j : ℕ, y ^ b = y ^ a * y ^ (2 * j) := by
  refine ⟨2 ^ (n - 1) * (b + (2 ^ n - 2) * a), ?_⟩
  have h2n : 2 * (2 ^ (n - 1) * (b + (2 ^ n - 2) * a)) = 2 ^ n * (b + (2 ^ n - 2) * a) := by
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel (by have := h.two_le; omega)]
  rw [h2n, pow_mul, h.y_pow_two_pow, ← pow_add]
  have h3 : a + (b + (2 ^ n - 2) * a) = b + (2 ^ n - 1) * a := by
    have : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by have := h.two_le; omega)
    have h4 : 2 ^ n - 1 = (2 ^ n - 2) + 1 := by omega
    rw [h4]
    ring
  rw [h3, pow_add, pow_mul, h.y_pow_sub_one, one_pow, mul_one]

theorem trick (θ : U →* U) (hθA : ∀ u, θ u ∈ fixSubgroup t) (hθy : ∀ u, θ (y u) = y (θ u))
    {f : U → U} (hfA : ∀ u, f u ∈ fixSubgroup t) (hfy : ∀ u, f (y u) = y (f u))
    (hf : ∀ u v, θ u = θ v → f u = f v) :
    (∀ u, f u = 1) ∨ ∃ k : ℕ, ∀ u, f u = (y ^ k) (θ u) := by
  have hf1 : f 1 = 1 := by
    have h1 := hfy 1
    rw [map_one] at h1
    exact h.eq_one_of_y_fix (hfA 1) h1.symm
  have hker : ∀ u, θ u = 1 → f u = 1 := fun u hu => by
    rw [hf u 1 (by rw [hu, map_one]), hf1]
  by_cases hθ : ∀ u, θ u = 1
  · exact Or.inl fun u => hker u (hθ u)
  push Not at hθ
  obtain ⟨g₀, hg₀⟩ := hθ
  have horb : ∀ u, θ u ≠ 1 → ∃ k : ℕ, f u = (y ^ k) (f g₀) ∧ θ u = (y ^ k) (θ g₀) := by
    intro u hu
    obtain ⟨k, hk⟩ := h.exists_pow_eq (hθA g₀) (hθA u) hg₀ hu
    refine ⟨k, ?_, hk.symm⟩
    rw [← map_pow_of_comm hfy]
    exact hf u _ (by rw [map_pow_of_comm hθy, hk])
  by_cases hf0 : f g₀ = 1
  · left
    intro u
    by_cases hu : θ u = 1
    · exact hker u hu
    obtain ⟨k, hk, -⟩ := horb u hu
    rw [hk, hf0, map_one]
  · right
    obtain ⟨i, hi⟩ := h.exists_pow_eq (hθA g₀) (hfA g₀) hg₀ hf0
    refine ⟨i, fun u => ?_⟩
    by_cases hu : θ u = 1
    · rw [hker u hu, hu, map_one]
    obtain ⟨k, hk, hk'⟩ := horb u hu
    rw [hk, hk', ← hi, pow_pow_apply_comm]

theorem trick_mul (θ : U →* U) (hθA : ∀ u, θ u ∈ fixSubgroup t) (hθy : ∀ u, θ (y u) = y (θ u))
    {f : U → U} (hfA : ∀ u, f u ∈ fixSubgroup t) (hfy : ∀ u, f (y u) = y (f u))
    (hf : ∀ u v, θ u = θ v → f u = f v) (u v : U) : f (u * v) = f u * f v := by
  rcases h.trick θ hθA hθy hfA hfy hf with h1 | ⟨k, hk⟩
  · rw [h1, h1, h1, mul_one]
  · rw [hk, hk, hk, map_mul, map_mul]

theorem trick_bilin (θ : U →* U) (hθA : ∀ u, θ u ∈ fixSubgroup t)
    (hθy : ∀ u, θ (y u) = y (θ u)) {β : U → U → U} (hβA : ∀ u v, β u v ∈ fixSubgroup t)
    (hβl : ∀ u v w, β (u * v) w = β u w * β v w) (hβr : ∀ u v w, β u (v * w) = β u v * β u w)
    (hβy : ∀ u v, β (y u) (y v) = y (β u v)) (hβalt : ∀ u, β u u = 1)
    (hβθ : ∀ u v, θ u = 1 → β u v = 1) (u v : U) : β u v = 1 := by
  have hskew : ∀ u v, β u v * β v u = 1 := fun u v => by
    have h1 := hβalt (u * v)
    rw [hβl, hβr, hβr, hβalt, hβalt, one_mul, mul_one] at h1
    exact h1
  have hβθ' : ∀ u v, θ v = 1 → β u v = 1 := fun u v hv => by
    have h1 := hskew u v
    rwa [hβθ v u hv, mul_one] at h1
  have hθ1 : ∀ u u', θ u = θ u' → θ (u⁻¹ * u') = 1 := fun u u' hu => by
    rw [map_mul, map_inv, hu, inv_mul_cancel]
  have hfib1 : ∀ u u' w, θ u = θ u' → β u w = β u' w := fun u u' w hu => by
    rw [show u' = u * (u⁻¹ * u') by group, hβl, hβθ _ _ (hθ1 u u' hu), mul_one]
  have hfib2 : ∀ u w w', θ w = θ w' → β u w = β u w' := fun u w w' hw => by
    rw [show w' = w * (w⁻¹ * w') by group, hβr, hβθ' _ _ (hθ1 w w' hw), mul_one]
  have hyj : ∀ (j : ℕ) (u : U), (y ^ j) (y u) = y ((y ^ j) u) := fun j u => by
    have h1 := pow_pow_apply_comm y j 1 u
    rwa [pow_one] at h1
  have key : ∀ (j : ℕ) (u v : U), β u ((y ^ j) v) * β v ((y ^ j) u) = 1 := by
    intro j u v
    have hm := h.trick_mul θ hθA hθy (f := fun u => β u ((y ^ j) u)) (fun u => hβA _ _)
      (fun u => by rw [hyj, hβy]) (fun u v huv => by
        rw [hfib1 u v _ huv]
        exact hfib2 v _ _ (by rw [map_pow_of_comm hθy, map_pow_of_comm hθy, huv])) u v
    simp only [map_mul, hβl, hβr] at hm
    have h2 : β u ((y ^ j) u) * ((β u ((y ^ j) v) * β v ((y ^ j) u)) * β v ((y ^ j) v)) =
        β u ((y ^ j) u) * (1 * β v ((y ^ j) v)) := by
      rw [one_mul, ← hm]
      group
    exact mul_right_cancel (mul_left_cancel h2)
  by_cases hθ : ∀ u, θ u = 1
  · exact hβθ u v (hθ u)
  push Not at hθ
  obtain ⟨g₀, hg₀⟩ := hθ
  have hsq : ∀ j : ℕ, β g₀ ((y ^ (2 * j)) g₀) = 1 := fun j => by
    have h1 := key j g₀ ((y ^ j) g₀)
    rwa [hβalt, mul_one, ← MulAut.mul_apply, ← pow_add, ← two_mul] at h1
  have hpow : ∀ (a : ℕ) (u v : U), β ((y ^ a) u) ((y ^ a) v) = (y ^ a) (β u v) := by
    intro a
    induction a with
    | zero => intro u v; rfl
    | succ a ih =>
      intro u v
      rw [pow_succ', MulAut.mul_apply, MulAut.mul_apply, hβy, ih, MulAut.mul_apply]
  by_cases hu : θ u = 1
  · exact hβθ u v hu
  by_cases hv : θ v = 1
  · exact hβθ' u v hv
  obtain ⟨a, ha⟩ := h.exists_pow_eq (hθA g₀) (hθA u) hg₀ hu
  obtain ⟨b, hb⟩ := h.exists_pow_eq (hθA g₀) (hθA v) hg₀ hv
  obtain ⟨j, hj⟩ := h.exists_pow_eq_pow_mul_sq a b
  rw [hfib1 u ((y ^ a) g₀) v (by rw [map_pow_of_comm hθy, ha]),
    hfib2 _ v ((y ^ b) g₀) (by rw [map_pow_of_comm hθy, hb]), hj, MulAut.mul_apply, hpow,
    hsq, map_one]

end Hyp

end CFSG.SeitzReduction.RankOne.Finkelstein
