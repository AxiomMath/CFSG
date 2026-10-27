module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

public section

namespace CFSG.LocalAnalysis.EvenBN.U5

namespace LinCase

open Subgroup

theorem dih39_core {G : Type*} [Group G] {y z k : G} (hy : y * y = 1) (hz : z * z = 1)
    (hk : k = y * z) {t : ℕ} (ht : k ^ (2 * t + 1) = 1) :
    k ^ (t + 1) * z * (k ^ (t + 1))⁻¹ = y := by
  have h1 : y * k = z := by
    rw [hk, ← mul_assoc, hy, one_mul]
  have h2 : k⁻¹ * y = z := by
    rw [hk, mul_inv_rev, inv_eq_of_mul_eq_one_right hz, inv_eq_of_mul_eq_one_right hy,
      mul_assoc, hy, mul_one]
  have hyk : y * k = k⁻¹ * y := h1.trans h2.symm
  have hpow : ∀ m : ℕ, y * k ^ m = (k ^ m)⁻¹ * y := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc y * k ^ (m + 1) = (y * k ^ m) * k := by rw [pow_succ, mul_assoc]
        _ = (k ^ m)⁻¹ * (y * k) := by rw [ih, mul_assoc]
        _ = (k ^ m)⁻¹ * (k⁻¹ * y) := by rw [hyk]
        _ = (k ^ m)⁻¹ * k⁻¹ * y := by rw [mul_assoc]
        _ = (k * k ^ m)⁻¹ * y := by rw [mul_inv_rev]
        _ = (k ^ (m + 1))⁻¹ * y := by rw [← pow_succ']
  have hinv : (k ^ (t + 1))⁻¹ = k ^ t := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_add, show t + 1 + t = 2 * t + 1 by ring]
    exact ht
  have hkz : k ^ (t + 1) * z = k ^ t * y := by
    rw [← h2, pow_succ, mul_assoc, mul_inv_cancel_left]
  rw [hinv, hkz, mul_assoc, hpow t, mul_inv_cancel_left]

theorem invol_conj_of_odd_ker {M Λ : Type*} [Group M] [Group Λ] (π : M →* Λ)
    (hker : Odd (Nat.card π.ker)) {y z : M} (hy : y * y = 1) (hz : z * z = 1)
    (hconj : ∃ m : M, π (m * z * m⁻¹) = π y) : ∃ u : M, u * z * u⁻¹ = y := by
  obtain ⟨m, hm⟩ := hconj
  obtain ⟨z', hz'⟩ : ∃ z' : M, z' = m * z * m⁻¹ := ⟨_, rfl⟩
  have hz'2 : z' * z' = 1 := by
    rw [hz']
    calc m * z * m⁻¹ * (m * z * m⁻¹) = m * (z * z) * m⁻¹ := by group
      _ = 1 := by rw [hz, mul_one, mul_inv_cancel]
  have hpz : π z' = π y := by rw [hz']; exact hm
  obtain ⟨k, hk⟩ : ∃ k : M, k = y * z' := ⟨_, rfl⟩
  have hkker : k ∈ π.ker := by
    rw [MonoidHom.mem_ker, hk, map_mul, hpz, ← map_mul, hy, map_one]
  have hodd : Odd (orderOf k) :=
    Odd.of_dvd_nat hker (Subgroup.orderOf_dvd_natCard π.ker hkker)
  obtain ⟨t, ht⟩ := hodd
  have hkpow : k ^ (2 * t + 1) = 1 := by
    rw [← ht]
    exact pow_orderOf_eq_one k
  refine ⟨k ^ (t + 1) * m, ?_⟩
  calc k ^ (t + 1) * m * z * (k ^ (t + 1) * m)⁻¹
      = k ^ (t + 1) * (m * z * m⁻¹) * (k ^ (t + 1))⁻¹ := by group
    _ = k ^ (t + 1) * z' * (k ^ (t + 1))⁻¹ := by rw [hz']
    _ = y := dih39_core hy hz'2 hk hkpow

end LinCase

end CFSG.LocalAnalysis.EvenBN.U5
