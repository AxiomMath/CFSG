module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem fzrAux_exists_relIndex_two_of_lt {N A : Subgroup G} (hA : IsPGroup 2 ↥A)
    (hNA : N ≤ A) (hne : N ≠ A) :
    ∃ D : Subgroup G, N ≤ D ∧ D ≤ A ∧ D.relIndex A = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (hA.to_le hNA).exists_card_eq
  obtain ⟨b, hb⟩ := hA.exists_card_eq
  have hab : a < b := by
    have hle : a ≤ b := by
      have := Subgroup.card_le_of_le hNA
      rw [ha, hb] at this
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
    refine lt_of_le_of_ne hle fun h => hne ?_
    refine Subgroup.eq_of_le_of_card_ge hNA ?_
    rw [ha, hb, h]
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  obtain ⟨K, hK, hNK, hKA⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two
    (n := c) (H := N) (L := A) (by rw [ha]; exact pow_dvd_pow 2 (by omega))
    (by rw [hb]; exact pow_dvd_pow 2 (Nat.le_succ c)) hNA
  refine ⟨K, hNK, hKA, ?_⟩
  have h : K.relIndex A * Nat.card ↥K = Nat.card ↥A := by
    have := Subgroup.relIndex_mul_card (H := K) (K := A)
    rwa [inf_eq_left.2 hKA] at this
  rw [hK, hb] at h
  have h' : K.relIndex A * 2 ^ c = 2 * 2 ^ c := by rw [h]; ring
  exact Nat.eq_of_mul_eq_mul_right (by positivity) h'

theorem fzr_chain {S H : Subgroup G} (hS : IsPGroup 2 S) (hHS : H ≤ S)
    (hidx : H.relIndex S ≤ 4) :
    ∃ M : Subgroup G, H ≤ M ∧ M ≤ S ∧ M.relIndex S ≤ 2 ∧ H.relIndex M ≤ 2 := by
  by_cases h2 : H.relIndex S ≤ 2
  · exact ⟨S, hHS, le_rfl, by rw [Subgroup.relIndex_self]; norm_num, h2⟩
  · push Not at h2
    have hne : H ≠ S := by
      intro hEq
      rw [hEq, Subgroup.relIndex_self] at h2
      omega
    obtain ⟨M, hHM, hMS, hMrel⟩ := fzrAux_exists_relIndex_two_of_lt hS hHS hne
    refine ⟨M, hHM, hMS, by omega, ?_⟩
    have hmul := Subgroup.relIndex_mul_relIndex H M S hHM hMS
    rw [hMrel] at hmul
    omega

theorem fzr_mul_mem_iff {S M : Subgroup G} (hMS : M ≤ S) (h : M.relIndex S ≤ 2) {a b : G}
    (ha : a ∈ S) (hb : b ∈ S) : a * b ∈ M ↔ (a ∈ M ↔ b ∈ M) := by
  by_cases h1 : M.relIndex S = 1
  · rw [Subgroup.relIndex_eq_one] at h1
    exact ⟨fun _ => ⟨fun _ => h1 hb, fun _ => h1 ha⟩, fun _ => h1 (S.mul_mem ha hb)⟩
  · have hpos : M.relIndex S ≠ 0 := by
      haveI : M.IsFiniteRelIndex S :=
        Subgroup.isFiniteRelIndex_iff_finiteIndex.mpr inferInstance
      exact Subgroup.relIndex_ne_zero
    have h2 : M.relIndex S = 2 := by omega
    have hindex : (M.subgroupOf S).index = 2 := h2
    have key := Subgroup.mul_mem_iff_of_index_two (H := M.subgroupOf S) hindex
      (a := (⟨a, ha⟩ : S)) (b := (⟨b, hb⟩ : S))
    exact key

end CFSG.OddStandard.SmallF3.FritzII
