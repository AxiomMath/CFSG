module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointTriple

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open Subgroup

structure FxData {G F : Type} [Group G] [Field F] (f : F → G) (x : G) : Prop where
  pow_three : x ^ 3 = 1
  add : ∀ s t, f (s + t) = f s * f t
  inj : Function.Injective f
  comm : ∀ t, f t * x = x * f t
  ne : ∀ t, f t ≠ x

namespace FxData

variable {G F : Type} [Group G] [Field F] {f : F → G} {x : G}

theorem f_zero (h : FxData f x) : f 0 = 1 := by
  have h1 := h.add 0 0
  rw [add_zero] at h1
  exact mul_left_cancel (h1.symm.trans (mul_one (f 0)).symm)

theorem f_neg (h : FxData f x) (t : F) : f (-t) = (f t)⁻¹ :=
  eq_inv_of_mul_eq_one_right (by rw [← h.add, add_neg_cancel, h.f_zero])

theorem comm_pow (h : FxData f x) (t : F) (e : ℕ) : f t * x ^ e = x ^ e * f t :=
  (Commute.pow_right (show Commute (f t) x from h.comm t) e).eq

theorem x_sq (h : FxData f x) : x ^ 2 = x⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  calc x * x ^ 2 = x ^ 3 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = 1 := h.pow_three

theorem f_pow_three [CharP F 3] (h : FxData f x) (t : F) : f t ^ 3 = 1 := by
  have h3F : (3 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 3
  have h1 : t + t + t = 0 := by linear_combination t * h3F
  calc f t ^ 3 = f t * f t * f t := by simp only [pow_succ, pow_zero, one_mul]
    _ = f (t + t + t) := by rw [h.add, h.add]
    _ = 1 := by rw [h1, h.f_zero]

theorem fx_pow_three [CharP F 3] (h : FxData f x) (u : F) (e : ℕ) : (f u * x ^ e) ^ 3 = 1 := by
  rw [(show Commute (f u) (x ^ e) from h.comm_pow u e).mul_pow, h.f_pow_three, ← pow_mul,
    mul_comm, pow_mul, h.pow_three, one_pow, one_mul]

theorem fx_ne_one (h : FxData f x) {u : F} (hu : u ≠ 0) {e : ℕ} (he : e ≤ 1) :
    f u * x ^ e ≠ 1 := fun h1 => by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp he with rfl | rfl
  · rw [pow_zero, mul_one, ← h.f_zero] at h1
    exact hu (h.inj h1)
  · rw [pow_one] at h1
    exact h.ne (-u) (by rw [h.f_neg]; exact (eq_inv_of_mul_eq_one_right h1).symm)

theorem fx_mem_zpowers [CharP F 3] (h : FxData f x) {u v : F} {e : ℕ} (he : e ≤ 1) (hv : v ≠ 0)
    (hmem : f v * x ^ e ∈ zpowers (f u * x ^ e)) : v = u ∨ (e = 0 ∧ v = -u) := by
  rcases mem_zpowers_of_pow_three (h.fx_pow_three u e) hmem with h1 | h2 | h3'
  · exact absurd h1 (h.fx_ne_one hv he)
  · left
    exact h.inj (mul_right_cancel h2)
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp he with rfl | rfl
    · right
      refine ⟨rfl, ?_⟩
      rw [pow_zero, mul_one, mul_one, ← h.f_neg] at h3'
      exact h.inj h3'
    · exfalso
      have h4 : (f v * x ^ 1) * (f u * x ^ 1) = 1 := by rw [h3']; exact inv_mul_cancel _
      have h5 : f (v + u) * x ^ 2 = 1 := by
        calc f (v + u) * x ^ 2 = f v * (f u * x) * x := by
              rw [h.add]; simp only [pow_two, mul_assoc]
          _ = f v * (x * f u) * x := by rw [h.comm u]
          _ = (f v * x ^ 1) * (f u * x ^ 1) := by simp only [pow_one, mul_assoc]
          _ = 1 := h4
      rw [h.x_sq] at h5
      exact h.ne (v + u) (mul_inv_eq_one.mp h5)

theorem exists_normal_form (h : FxData f x) {t : F} (ht : t ≠ 0) {i : ℕ} (hi : i < 3) :
    ∃ (k : F) (e : ℕ), k ≠ 0 ∧ e ≤ 1 ∧ zpowers (f t * x ^ i) = zpowers (f k * x ^ e) := by
  interval_cases i
  · exact ⟨t, 0, ht, by omega, rfl⟩
  · exact ⟨t, 1, ht, le_rfl, rfl⟩
  · refine ⟨-t, 1, neg_ne_zero.mpr ht, le_rfl, ?_⟩
    have hinv : (f t * x ^ 2)⁻¹ = f (-t) * x ^ 1 := by
      rw [mul_inv_rev, h.x_sq, inv_inv, ← h.f_neg, pow_one]
      exact (h.comm (-t)).symm
    rw [← zpowers_inv, hinv]

end FxData

end CFSG.LocalAnalysis.RankFourTheoremC
