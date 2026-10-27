module

public import Mathlib.GroupTheory.Perm.Centralizer

public section

namespace CFSG.EvenSporadicStandard.TwoHS.SignS9

open Equiv Equiv.Perm
open scoped Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem ten_le_card_cycleType_eq (hα : Fintype.card α = 5) {z : Perm α} (hz : orderOf z = 2) :
    10 ≤ #{g : Perm α | g.cycleType = z.cycleType} := by
  obtain ⟨n, hn⟩ := cycleType_prime_order (σ := z) (by rw [hz]; exact Nat.prime_two)
  rw [hz] at hn
  have hsum : z.cycleType.sum ≤ Fintype.card α := sum_cycleType_le z
  rw [hn, Multiset.sum_replicate, hα] at hsum
  have h01 : n = 0 ∨ n = 1 := by simp at hsum; omega
  rw [card_of_cycleType, hn]
  rcases h01 with rfl | rfl
  · simp [hα]
    decide
  · simp [hα]
    decide

theorem eq_bot_of_normal_card_dvd_eight (hα : Fintype.card α = 5) (K : Subgroup (Perm α))
    [K.Normal] (hK : Nat.card K ∣ 8) : K = ⊥ := by
  by_contra hne
  have h2 : 2 ∣ Nat.card K := by
    obtain ⟨i, -, hcard⟩ :=
      (Nat.dvd_prime_pow Nat.prime_two).1 (by simpa using hK : Nat.card K ∣ 2 ^ 3)
    rcases i with _ | i
    · exact absurd (Subgroup.card_eq_one.1 (by simpa using hcard)) hne
    · rw [hcard]
      exact dvd_pow_self 2 (Nat.succ_ne_zero i)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hz' : orderOf (z : Perm α) = 2 := by rw [Subgroup.orderOf_coe, hz]
  classical
  have hsub : ({g : Perm α | g.cycleType = (z : Perm α).cycleType} : Finset (Perm α)) ⊆
      (Finset.univ.filter (· ∈ K)) := by
    intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    obtain ⟨c, hc⟩ := isConj_iff.1 (isConj_iff_cycleType_eq.2 hg.symm)
    rw [← hc]
    exact Subgroup.Normal.conj_mem inferInstance _ z.2 c
  have hle := Finset.card_le_card hsub
  have h10 := ten_le_card_cycleType_eq hα hz'
  have hKcard : (Finset.univ.filter (· ∈ K)).card = Nat.card K := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h8 : Nat.card K ≤ 8 := Nat.le_of_dvd (by norm_num) hK
  omega

end CFSG.EvenSporadicStandard.TwoHS.SignS9
