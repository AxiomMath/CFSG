module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitSevenPerm

public section

namespace CFSG.ComponentClassification.HSFLit

open Equiv Equiv.Perm Subgroup
open scoped Pointwise

theorem exists_eq_of_mem_centralizer_rho {σ : Perm (Fin 7)}
    (hσ : σ ∈ centralizer ({rho0} : Set (Perm (Fin 7)))) :
    ∃ i < 4, ∃ j < 2, σ = a0 ^ i * c0 ^ j := by
  classical
  rw [centralizer_rho0_eq] at hσ
  have hcN : zpowers c0 ≤ normalizer (zpowers a0 : Set (Perm (Fin 7))) := by
    rw [zpowers_le]
    exact centralizer_le_normalizer _ (by
      rw [mem_centralizer_iff]
      intro g hg
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
      exact ((Commute.zpow_left a0_c0_comm k)).eq)
  have hσ' : σ ∈ (zpowers a0 : Set (Perm (Fin 7))) * (zpowers c0 : Set (Perm (Fin 7))) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hcN]
    exact hσ
  obtain ⟨u, hu, v, hv, rfl⟩ := hσ'
  rw [SetLike.mem_coe, mem_zpowers_iff_mem_range_orderOf, orderOf_a0] at hu
  rw [SetLike.mem_coe, mem_zpowers_iff_mem_range_orderOf,
    orderOf_eq_prime (by decide : c0 ^ 2 = 1) (by decide : c0 ≠ 1)] at hv
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
  exact ⟨i, Finset.mem_range.mp hi, j, Finset.mem_range.mp hj, rfl⟩

theorem mem_P0_iff_exists (σ : Perm (Fin 7)) :
    σ ∈ P0 ↔ ∃ i < 4, ∃ j < 2, ∃ k < 2, σ = a0 ^ i * c0 ^ j * b0 ^ k := by
  constructor
  · intro hσ
    rcases (mem_P0_iff σ).mp hσ with h1 | h1
    · obtain ⟨i, hi, j, hj, h⟩ := exists_eq_of_mem_centralizer_rho h1
      exact ⟨i, hi, j, hj, 0, by norm_num, by rw [pow_zero, mul_one]; exact h⟩
    · obtain ⟨i, hi, j, hj, h⟩ := exists_eq_of_mem_centralizer_rho h1
      refine ⟨i, hi, j, hj, 1, by norm_num, ?_⟩
      rw [pow_one, ← h, mul_assoc, show b0 * b0 = 1 by decide, mul_one]
  · rintro ⟨i, -, j, -, k, -, rfl⟩
    exact mul_mem (mul_mem (pow_mem a0_mem_P0 i) (pow_mem c0_mem_P0 j)) (pow_mem b0_mem_P0 k)

theorem b0_a0_b0 : b0 * a0 * b0⁻¹ = a0⁻¹ := by decide

theorem c0_sq : c0 ^ 2 = 1 := by decide

theorem a0_pow_four : a0 ^ 4 = 1 := by
  rw [← orderOf_a0]
  exact pow_orderOf_eq_one a0

theorem sq_a0_pow_c0_pow_b0 (i j : ℕ) : (a0 ^ i * c0 ^ j * b0) ^ 2 = 1 := by
  have hconj : b0 * (a0 ^ i * c0 ^ j) * b0⁻¹ = a0⁻¹ ^ i * c0 ^ j := by
    have h := map_mul (MulAut.conj b0) (a0 ^ i) (c0 ^ j)
    simp only [map_pow, MulAut.conj_apply] at h
    rw [h, b0_a0_b0, show b0 * c0 * b0⁻¹ = c0 by decide]
  have hb : b0 * b0 = 1 := by decide
  have hac : Commute a0 c0 := a0_c0_comm
  have hcomm : Commute (c0 ^ j) (a0⁻¹ ^ i) := hac.symm.inv_right.pow_pow j i
  calc (a0 ^ i * c0 ^ j * b0) ^ 2
      = a0 ^ i * c0 ^ j * (b0 * (a0 ^ i * c0 ^ j) * b0⁻¹) * (b0 * b0) := by
        rw [sq]; simp only [mul_assoc, inv_mul_cancel_left]
    _ = a0 ^ i * (c0 ^ j * a0⁻¹ ^ i) * c0 ^ j := by
        rw [hconj, hb, mul_one]; simp only [mul_assoc]
    _ = a0 ^ i * a0⁻¹ ^ i * (c0 ^ j * c0 ^ j) := by
        rw [hcomm.eq]; simp only [mul_assoc]
    _ = 1 := by
        rw [inv_pow, mul_inv_cancel, one_mul, ← pow_add, ← two_mul, pow_mul, c0_sq, one_pow]

theorem pow_four_eq_one_of_mem_P0 {σ : Perm (Fin 7)} (hσ : σ ∈ P0) : σ ^ 4 = 1 := by
  obtain ⟨i, -, j, -, k, hk, rfl⟩ := (mem_P0_iff_exists σ).mp hσ
  have hac : Commute a0 c0 := a0_c0_comm
  interval_cases k
  · rw [pow_zero, mul_one, (hac.pow_pow i j).mul_pow, ← pow_mul, ← pow_mul, mul_comm i 4,
      pow_mul, a0_pow_four, one_pow, one_mul, show j * 4 = 2 * (2 * j) by ring, pow_mul,
      c0_sq, one_pow]
  · rw [pow_one, show 4 = 2 * 2 by rfl, pow_mul, sq_a0_pow_c0_pow_b0, one_pow]

theorem a0_b0_mem_R0 : a0 * b0 ∈ R0 :=
  ⟨mul_mem a0_mem_P0 b0_mem_P0, by
    change _ ∈ alternatingGroup (Fin 7)
    rw [Perm.mem_alternatingGroup]
    decide⟩

theorem c0_b0_mem_R0 : c0 * b0 ∈ R0 :=
  ⟨mul_mem c0_mem_P0 b0_mem_P0, by
    change _ ∈ alternatingGroup (Fin 7)
    rw [Perm.mem_alternatingGroup]
    decide⟩

theorem a0_sq_mem_R0 : a0 ^ 2 ∈ R0 :=
  ⟨pow_mem a0_mem_P0 2, by
    change _ ∈ alternatingGroup (Fin 7)
    rw [Perm.mem_alternatingGroup]
    decide⟩

theorem a0_b0_c0_b0_ne : a0 * b0 * (c0 * b0) ≠ c0 * b0 * (a0 * b0) := by decide

theorem sq_eq_one_of_mem_P0_of_commute {σ : Perm (Fin 7)} (hσ : σ ∈ P0)
    (h : σ * (c0 * b0) = c0 * b0 * σ) : σ ^ 2 = 1 := by
  obtain ⟨i, hi, j, hj, k, hk, rfl⟩ := (mem_P0_iff_exists σ).mp hσ
  interval_cases k
  · rw [pow_zero, mul_one] at h ⊢
    revert h
    interval_cases i <;> interval_cases j <;> decide
  · rw [pow_one]
    exact sq_a0_pow_c0_pow_b0 i j

theorem a0_sq_comm_of_mem_P0 {σ : Perm (Fin 7)} (hσ : σ ∈ P0) : a0 ^ 2 * σ = σ * a0 ^ 2 := by
  obtain ⟨i, hi, j, hj, k, hk, rfl⟩ := (mem_P0_iff_exists σ).mp hσ
  interval_cases i <;> interval_cases j <;> interval_cases k <;> decide

theorem c0_not_mem_R0 : c0 ∉ R0 := fun h => c0_not_mem_alternating h.2

theorem mul_c0_mem_R0_of_not_mem {σ : Perm (Fin 7)} (hσ : σ ∈ P0) (hσR : σ ∉ R0) :
    σ * c0 ∈ R0 :=
  (mem_R0_or_mul_c0_mem_R0 hσ).resolve_left hσR

end CFSG.ComponentClassification.HSFLit
