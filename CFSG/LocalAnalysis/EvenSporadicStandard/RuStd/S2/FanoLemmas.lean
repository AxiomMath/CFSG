module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2.Fano

open Subgroup

variable {G : Type*} [Group G]

theorem exists_mem_ne_of_card_four {K : Subgroup G} (hK : Nat.card K = 4) (a b : G) :
    ∃ y ∈ K, y ≠ a ∧ y ≠ b := by
  classical
  by_contra h
  push Not at h
  have hKfin : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have hsub : (K : Set G) ⊆ ({a, b} : Set G) := by
    intro y hy
    by_cases hya : y = a
    · exact Or.inl hya
    · exact Or.inr (h y hy hya)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({a, b} : Set G).ncard ≤ 2 := by
    calc ({a, b} : Set G).ncard ≤ ({b} : Set G).ncard + 1 := Set.ncard_insert_le a {b}
      _ = 2 := by rw [Set.ncard_singleton]
  have h3 : Nat.card (K : Set G) = 4 := hK
  rw [Nat.card_coe_set_eq] at h3
  omega

theorem eq_of_four_distinct {K : Subgroup G} (hK : Nat.card K = 4) {a b c d : G}
    (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K) (hd : d ∈ K)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ∀ y ∈ K, y = a ∨ y = b ∨ y = c ∨ y = d := by
  classical
  intro y hy
  by_contra hne
  simp only [not_or] at hne
  obtain ⟨hya, hyb, hyc, hyd⟩ := hne
  have hKfin : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have hfin : (K : Set G).Finite := Set.toFinite _
  have hsub : (({a, b, c, d, y} : Finset G) : Set G) ⊆ K := by
    intro z hz
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl <;> assumption
  have h1 := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_coe_finset, ← Nat.card_coe_set_eq] at h1
  have h5 : ({a, b, c, d, y} : Finset G).card = 5 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton] <;> simp [*, Ne.symm]
  have : Nat.card (K : Set G) = 4 := hK
  omega

theorem inv_mul_mem_of_index_two {A B : Subgroup G} (hBA : B ≤ A) (hA : Nat.card A = 8)
    (hB : Nat.card B = 4) {x y : G} (hx : x ∈ A) (hxB : x ∉ B) (hy : y ∈ A) (hyB : y ∉ B) :
    x⁻¹ * y ∈ B := by
  have h1 := relIndex_mul_card (H := B) (K := A)
  rw [inf_of_le_left hBA, hB, hA] at h1
  have h2 : (B.subgroupOf A).index = 2 := by
    have : B.relIndex A = 2 := by omega
    exact this
  have h3 := (mul_mem_iff_of_index_two h2 (a := ⟨x⁻¹, A.inv_mem hx⟩) (b := ⟨y, hy⟩))
  simp only [mem_subgroupOf, MulMemClass.mk_mul_mk] at h3
  rw [show x⁻¹ * y ∈ B ↔ _ from h3]
  simp [hyB, hxB]

theorem mul_comm_of_mul_self_eq_one {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : (x * y) * (x * y) = 1) : x * y = y * x := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have h := inv_eq_of_mul_eq_one_right hxy
  rw [mul_inv_rev, hxi, hyi] at h
  exact h.symm

end CFSG.EvenSporadicStandard.RuStd.S2.Fano
