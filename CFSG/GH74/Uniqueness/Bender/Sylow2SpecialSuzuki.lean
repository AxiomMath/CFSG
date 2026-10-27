module

public import CFSG.GH74.Uniqueness.Bender.Sylow2Special
public import CFSG.GH74.Uniqueness.Bender.Suzuki

public section

namespace CFSG.GH74.Uniqueness.Bender

open Subgroup CFSG CFSG.ProperTwoGeneratedCore.Lemma37

section Suzuki

variable {K : Type*} [Group K] [Finite K]

theorem BenderType.sq_mem_rootCenter_suzuki
    {n : ℕ} (h : BenderType K n 2 1) (Q : Sylow 2 K)
    {x : K} (hx : x ∈ (Q : Subgroup K)) : x * x ∈ rootCenter (Q : Subgroup K) := by
  obtain ⟨t, hc⟩ := h.exists_benderCore Q
  have hRD := h.suzuki_rootData Q
  have hn2 : 2 ≤ n := h.two_le.2
  have hq1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hcardP : Nat.card ↥(Q : Subgroup K) = 2 ^ n + (2 ^ n - 1) * 2 ^ n := by
    rw [hc.card_eq]
    obtain ⟨q', hq'⟩ : ∃ q', 2 ^ n = q' + 1 := ⟨2 ^ n - 1, by omega⟩
    rw [hq']
    simp only [Nat.add_sub_cancel]
    ring
  have hsq := sq_sq_eq_one_of_rootData hRD hcardP
  by_cases hxZ : x ∈ rootCenter (Q : Subgroup K)
  · have : x * x = 1 := hc.center_sq x hxZ
    rw [this]
    exact (rootCenter _).one_mem
  have h1 : x * x ≠ 1 := fun h1 => hxZ (hc.mem_rootCenter_of_mul_self hx h1)
  refine hc.mem_rootCenter_of_mul_self (Q.mul_mem hx hx) ?_
  have h2 := hsq ⟨x, hx⟩ (fun h => h1 (by simpa [sq] using congrArg Subtype.val h))
  simpa [sq] using congrArg Subtype.val h2

theorem BenderType.lemma_3_5_a
    {n i e : ℕ} (h : BenderType K n i e) (hi : 2 ≤ i)
    (Q : Sylow 2 K) :
    ⁅(Q : Subgroup K), (Q : Subgroup K)⁆ = rootCenter (Q : Subgroup K) ∧
      frattini ↥(Q : Subgroup K) = (rootCenter (Q : Subgroup K)).subgroupOf (Q : Subgroup K) ∧
      Subgroup.closure {x | x ∈ (Q : Subgroup K) ∧ x * x = 1} = rootCenter (Q : Subgroup K) ∧
      IsElementaryAbelian 2
        (↥(Q : Subgroup K) ⧸ (rootCenter (Q : Subgroup K)).subgroupOf (Q : Subgroup K)) ∧
      Nat.card (↥(Q : Subgroup K) ⧸
        (rootCenter (Q : Subgroup K)).subgroupOf (Q : Subgroup K)) = (2 ^ n) ^ (i - 1) := by
  rcases h.cases' with ⟨hi1, -, -⟩ | ⟨hi2, he, -⟩ | ⟨hi3, -, -⟩
  · omega
  · subst hi2
    subst he
    obtain ⟨t, hc⟩ := h.exists_benderCore Q
    have hn2 : 2 ≤ n := h.two_le.2
    have hq : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact hc.special_of_sq_mem Q.isPGroup' hi hq (fun x hx => h.sq_mem_rootCenter_suzuki Q hx)
  · subst hi3
    exact h.lemma_3_5_a_unitary Q

end Suzuki

end CFSG.GH74.Uniqueness.Bender
