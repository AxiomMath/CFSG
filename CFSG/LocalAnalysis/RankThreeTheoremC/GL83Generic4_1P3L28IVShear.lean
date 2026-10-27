module

public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Group

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup

theorem l28iv_shear {G : Type*} [Group G] {t y : G} (ht : orderOf t = 9) (hy3 : y ^ 3 = 1)
    (hyt : y * t * y⁻¹ ∈ zpowers t) (hne : y * t * y⁻¹ ≠ t) :
    t * (y * t * y⁻¹)⁻¹ ≠ 1 ∧ (t * (y * t * y⁻¹)⁻¹) ^ 3 = 1 ∧
      (t * (y * t * y⁻¹)⁻¹) * y = y * (t * (y * t * y⁻¹)⁻¹) ∧
      t * (y * t * y⁻¹)⁻¹ ∈ zpowers t ∧ t * y * t⁻¹ = (t * (y * t * y⁻¹)⁻¹) * y := by
  have hfin : IsOfFinOrder t := orderOf_pos_iff.mp (by rw [ht]; norm_num)
  obtain ⟨s, hs9, hs⟩ : ∃ s : ℕ, s < 9 ∧ t ^ s = y * t * y⁻¹ := by
    classical
    have h := hfin.mem_zpowers_iff_mem_range_orderOf.mp hyt
    rw [Finset.mem_image] at h
    obtain ⟨s, hs, hst⟩ := h
    exact ⟨s, by rw [Finset.mem_range, ht] at hs; exact hs, hst⟩
  have hpow : ∀ n : ℕ, y * t ^ n * y⁻¹ = t ^ (s * n) := fun n => by
    rw [← conj_pow, ← hs, ← pow_mul]
  have hy2 : y ^ 2 * t * (y ^ 2)⁻¹ = t ^ (s * s) := by
    calc y ^ 2 * t * (y ^ 2)⁻¹ = y * (y * t * y⁻¹) * y⁻¹ := by rw [pow_two]; group
      _ = y * t ^ s * y⁻¹ := by rw [← hs]
      _ = t ^ (s * s) := hpow s
  have hy3t : t ^ (s * s * s) = t := by
    have h : y ^ 3 * t * (y ^ 3)⁻¹ = t ^ (s * (s * s)) := by
      calc y ^ 3 * t * (y ^ 3)⁻¹ = y * (y ^ 2 * t * (y ^ 2)⁻¹) * y⁻¹ := by
            rw [pow_succ, pow_two]; group
        _ = y * t ^ (s * s) * y⁻¹ := by rw [hy2]
        _ = t ^ (s * (s * s)) := hpow (s * s)
    rw [hy3, one_mul, inv_one, mul_one] at h
    rw [mul_assoc]
    exact h.symm
  have hmod : s * s * s ≡ 1 [MOD 9] := by
    rw [← ht]
    exact (pow_eq_pow_iff_modEq).mp (by rw [hy3t, pow_one])
  have hs1 : s ≠ 1 := by
    rintro rfl
    exact hne (by rw [← hs, pow_one])
  have h9 : t ^ 9 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have hne1 : ∀ k : ℕ, 0 < k → k < 9 → t ^ k ≠ 1 := by
    intro k hk0 hk9 h
    have := orderOf_le_of_pow_eq_one hk0 h
    omega
  have hs47 : s = 4 ∨ s = 7 := by
    interval_cases s <;> revert hmod hs1 <;> decide
  rcases hs47 with rfl | rfl
  ·
    have hz : t * (y * t * y⁻¹)⁻¹ = t ^ 6 := by
      rw [← hs]
      have e : t = t ^ 6 * t ^ 4 := by rw [← pow_add, show 6 + 4 = 9 + 1 from rfl, pow_add, h9,
        one_mul, pow_one]
      calc t * (t ^ 4)⁻¹ = t ^ 6 * t ^ 4 * (t ^ 4)⁻¹ := by rw [← e]
        _ = t ^ 6 := by group
    rw [hz]
    refine ⟨hne1 6 (by norm_num) (by norm_num), ?_, ?_, pow_mem (mem_zpowers t) 6, ?_⟩
    · rw [← pow_mul, show 6 * 3 = 9 * 2 from rfl, pow_mul, h9, one_pow]
    · have h1 : y * t ^ 6 * y⁻¹ = t ^ 6 := by
        rw [hpow 6, show 4 * 6 = 9 * 2 + 6 from rfl, pow_add, pow_mul, h9, one_pow, one_mul]
      calc t ^ 6 * y = (y * t ^ 6 * y⁻¹) * y := by rw [h1]
        _ = y * t ^ 6 := by group
    · rw [← hz]
      group
  ·
    have hz : t * (y * t * y⁻¹)⁻¹ = t ^ 3 := by
      rw [← hs]
      have e : t = t ^ 3 * t ^ 7 := by rw [← pow_add, show 3 + 7 = 9 + 1 from rfl, pow_add, h9,
        one_mul, pow_one]
      calc t * (t ^ 7)⁻¹ = t ^ 3 * t ^ 7 * (t ^ 7)⁻¹ := by rw [← e]
        _ = t ^ 3 := by group
    rw [hz]
    refine ⟨hne1 3 (by norm_num) (by norm_num), ?_, ?_, pow_mem (mem_zpowers t) 3, ?_⟩
    · rw [← pow_mul, show 3 * 3 = 9 from rfl, h9]
    · have h1 : y * t ^ 3 * y⁻¹ = t ^ 3 := by
        rw [hpow 3, show 7 * 3 = 9 * 2 + 3 from rfl, pow_add, pow_mul, h9, one_pow, one_mul]
      calc t ^ 3 * y = (y * t ^ 3 * y⁻¹) * y := by rw [h1]
        _ = y * t ^ 3 := by group
    · rw [← hz]
      group

end CFSG.LocalAnalysis.RankThreeTheoremC
