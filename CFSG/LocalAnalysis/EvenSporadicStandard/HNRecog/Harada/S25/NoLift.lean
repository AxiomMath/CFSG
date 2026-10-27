module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.S25

open Subgroup

@[expose] def a1 : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 2 3

@[expose] def a2 : Equiv.Perm (Fin 5) := Equiv.swap 0 2 * Equiv.swap 1 3

theorem a1_sq : a1 * a1 = 1 := by
  decide +kernel

theorem a2_sq : a2 * a2 = 1 := by
  decide +kernel

theorem a1_a2_comm : a1 * a2 = a2 * a1 := by
  decide +kernel

theorem a1_mem : a1 ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

theorem a2_mem : a2 ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

@[expose] def NoLiftV4 {H : Type*} [Group H] (z : H)
    (ψ : ↥(centralizer ({z} : Set H)) →* Equiv.Perm (Fin 5)) : Prop :=
  ∀ u v : ↥(centralizer ({z} : Set H)), ψ u = a1 → ψ v = a2 →
    (u : H) ^ 2 ∈ zpowers z → (v : H) ^ 2 ∈ zpowers z →
      (u : H) * v * (u : H)⁻¹ * (v : H)⁻¹ ∈ zpowers z → False

theorem mem_zpowers_of_sq_eq_one {H : Type*} [Group H] {z : H} (hz : z ^ 2 = 1) (x : H) :
    x ∈ zpowers z ↔ x = 1 ∨ x = z := by
  rw [Subgroup.mem_zpowers_iff]
  have hz2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two, ← pow_two, hz]
  constructor
  · rintro ⟨k, rfl⟩
    have hk : k = 2 * (k / 2) + k % 2 := by omega
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [hk, h, add_zero, zpow_mul, hz2, one_zpow]
    · right
      rw [hk, h, zpow_add, zpow_mul, hz2, one_zpow, one_mul, zpow_one]
  · rintro (rfl | rfl)
    · exact ⟨0, zpow_zero _⟩
    · exact ⟨1, zpow_one _⟩

end CFSG.EvenSporadicStandard.HNRecog.Harada.S25
