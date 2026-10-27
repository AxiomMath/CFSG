module

public import CFSG.LocalAnalysis.AGLEmbedding.TrialityTwo.SevenProj

public section

namespace CFSG.AGLEmbedding.TrialityTwo.Seven

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {t : Module.End K V}

section Isometry

variable (hQt : ∀ v, Q (t v) = Q v)
include hQt

theorem map_pow_apply (n : ℕ) (v : V) : Q ((t ^ n) v) = Q v := by
  induction n with
  | zero => rw [pow_zero, Module.End.one_apply]
  | succ n ih => rw [pow_succ', Module.End.mul_apply, hQt, ih]

theorem polar_pow_apply_apply (n : ℕ) (x y : V) :
    polar Q ((t ^ n) x) ((t ^ n) y) = polar Q x y := by
  simp only [QuadraticMap.polar, ← map_add, map_pow_apply hQt]

theorem map_apply_add_self_eq_zero (h2 : (2 : K) = 0) {y : V} (hy : polar Q (t y) y = 0) :
    Q (t y + y) = 0 := by
  rw [QuadraticMap.map_add (⇑Q), hQt, hy, add_zero, ← two_mul, h2, zero_mul]

variable (h7 : t ^ 7 = 1)
include h7

theorem polar_pow_left {a : ℕ} (ha : a ≤ 7) (x y : V) :
    polar Q ((t ^ a) x) y = polar Q x ((t ^ (7 - a)) y) := by
  have hy : (t ^ a) ((t ^ (7 - a)) y) = y := by
    rw [← Module.End.mul_apply, ← pow_add, Nat.add_sub_cancel' ha, h7, Module.End.one_apply]
  conv_lhs => rw [← hy]
  exact polar_pow_apply_apply hQt a x _

theorem polar_projU₁_left (x y : V) : polar Q (projU₁ t x) y = polar Q x (projU₂ t y) := by
  have e1 : polar Q (t x) y = polar Q x ((t ^ 6) y) := by
    simpa using polar_pow_left hQt h7 (a := 1) (by norm_num) x y
  have e2 := polar_pow_left hQt h7 (a := 2) (by norm_num) x y
  have e4 := polar_pow_left hQt h7 (a := 4) (by norm_num) x y
  norm_num at e2 e4
  simp only [projU₁, projU₂, LinearMap.add_apply, Module.End.one_apply, polar_add_left,
    polar_add_right, e1, e2, e4]
  abel

theorem polar_projU₂_left (x y : V) : polar Q (projU₂ t x) y = polar Q x (projU₁ t y) := by
  rw [polar_comm, ← polar_projU₁_left hQt h7, polar_comm]

theorem polar_projC_left (x y : V) : polar Q (projC t x) y = polar Q x (projC t y) := by
  have e1 : polar Q (t x) y = polar Q x ((t ^ 6) y) := by
    simpa using polar_pow_left hQt h7 (a := 1) (by norm_num) x y
  have e2 := polar_pow_left hQt h7 (a := 2) (by norm_num) x y
  have e3 := polar_pow_left hQt h7 (a := 3) (by norm_num) x y
  have e4 := polar_pow_left hQt h7 (a := 4) (by norm_num) x y
  have e5 := polar_pow_left hQt h7 (a := 5) (by norm_num) x y
  have e6 := polar_pow_left hQt h7 (a := 6) (by norm_num) x y
  norm_num at e2 e3 e4 e5 e6
  simp only [projC, LinearMap.add_apply, Module.End.one_apply, polar_add_left, polar_add_right,
    e1, e2, e3, e4, e5, e6]
  abel

variable (h2 : (2 : K) = 0)
include h2

theorem polar_eq_zero_of_mem_spU₁ {x y : V} (hx : x ∈ spU₁ t) (hy : y ∈ spU₁ t) :
    polar Q x y = 0 := by
  rw [← (mem_spU₁_iff h7 h2).1 hx, polar_projU₁_left hQt h7, projU₂_apply_of_mem_spU₁ h7 h2 hy,
    polar_zero_right]

theorem polar_eq_zero_of_mem_spU₂ {x y : V} (hx : x ∈ spU₂ t) (hy : y ∈ spU₂ t) :
    polar Q x y = 0 := by
  rw [← (mem_spU₂_iff h7 h2).1 hx, polar_projU₂_left hQt h7, projU₁_apply_of_mem_spU₂ h7 h2 hy,
    polar_zero_right]

theorem polar_eq_zero_of_mem_fixC_of_mem_spU₁ {x y : V} (hx : x ∈ fixC t) (hy : y ∈ spU₁ t) :
    polar Q x y = 0 := by
  rw [← projC_apply_of_mem_fixC h7 h2 hx, polar_projC_left hQt h7,
    projC_apply_of_mem_spU₁ h7 h2 hy, polar_zero_right]

theorem polar_eq_zero_of_mem_fixC_of_mem_spU₂ {x y : V} (hx : x ∈ fixC t) (hy : y ∈ spU₂ t) :
    polar Q x y = 0 := by
  rw [← projC_apply_of_mem_fixC h7 h2 hx, polar_projC_left hQt h7,
    projC_apply_of_mem_spU₂ h7 h2 hy, polar_zero_right]

theorem map_eq_zero_of_mem_spU₁ {x : V} (hx : x ∈ spU₁ t) : Q x = 0 := by
  have hy : t (t x) + t x ∈ spU₁ t :=
    add_mem (apply_mem_spU₁ (apply_mem_spU₁ hx)) (apply_mem_spU₁ hx)
  rw [← eq_apply_add_of_mem_spU₁ h7 h2 hx]
  exact map_apply_add_self_eq_zero hQt h2
    (polar_eq_zero_of_mem_spU₁ hQt h7 h2 (apply_mem_spU₁ hy) hy)

theorem map_eq_zero_of_mem_spU₂ {x : V} (hx : x ∈ spU₂ t) : Q x = 0 := by
  have hy : t (t x) ∈ spU₂ t := apply_mem_spU₂ (apply_mem_spU₂ hx)
  rw [← eq_apply_add_of_mem_spU₂ h7 h2 hx]
  exact map_apply_add_self_eq_zero hQt h2
    (polar_eq_zero_of_mem_spU₂ hQt h7 h2 (apply_mem_spU₂ hy) hy)

variable (hB : (polarBilin Q).Nondegenerate)
include hB

theorem eq_zero_of_mem_spU₁_of_polar {x : V} (hx : x ∈ spU₁ t)
    (h : ∀ y ∈ spU₂ t, polar Q x y = 0) : x = 0 := by
  refine eq_zero_of_polar_eq_zero hB fun v => ?_
  rw [← projC_add_projU₁_add_projU₂_apply h7 h2 v, polar_add_right, polar_add_right, polar_comm,
    polar_eq_zero_of_mem_fixC_of_mem_spU₁ hQt h7 h2 (projC_apply_mem_fixC h7 h2 v) hx,
    polar_eq_zero_of_mem_spU₁ hQt h7 h2 hx (projU₁_apply_mem v), h _ (projU₂_apply_mem v),
    add_zero, add_zero]

theorem eq_zero_of_mem_spU₂_of_polar {x : V} (hx : x ∈ spU₂ t)
    (h : ∀ y ∈ spU₁ t, polar Q x y = 0) : x = 0 := by
  refine eq_zero_of_polar_eq_zero hB fun v => ?_
  rw [← projC_add_projU₁_add_projU₂_apply h7 h2 v, polar_add_right, polar_add_right, polar_comm,
    polar_eq_zero_of_mem_fixC_of_mem_spU₂ hQt h7 h2 (projC_apply_mem_fixC h7 h2 v) hx,
    polar_eq_zero_of_mem_spU₂ hQt h7 h2 hx (projU₂_apply_mem v), h _ (projU₁_apply_mem v),
    add_zero, zero_add]

theorem eq_zero_of_mem_fixC_of_polar {x : V} (hx : x ∈ fixC t)
    (h : ∀ y ∈ fixC t, polar Q x y = 0) : x = 0 := by
  refine eq_zero_of_polar_eq_zero hB fun v => ?_
  rw [← projC_add_projU₁_add_projU₂_apply h7 h2 v, polar_add_right, polar_add_right,
    polar_eq_zero_of_mem_fixC_of_mem_spU₁ hQt h7 h2 hx (projU₁_apply_mem v),
    polar_eq_zero_of_mem_fixC_of_mem_spU₂ hQt h7 h2 hx (projU₂_apply_mem v),
    h _ (projC_apply_mem_fixC h7 h2 v), add_zero, add_zero]

end Isometry

end CFSG.AGLEmbedding.TrialityTwo.Seven
