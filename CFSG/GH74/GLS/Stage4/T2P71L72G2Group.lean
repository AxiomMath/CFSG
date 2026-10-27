module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.IndexNormal

public section

namespace CFSG.GH74.GLS.Stage4.Rest.L72

open Subgroup
open scoped commutatorElement

theorem commutator_mem_of_index_le_three {U : Type*} [Group U] [Finite U] {k : ℕ} (hk : 1 ≤ k)
    (hU : Nat.card U = 3 ^ k) (B : Subgroup U) (hcard : Nat.card U ≤ 3 * Nat.card B) (x y : U) :
    ⁅x, y⁆ ∈ B := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 U := IsPGroup.of_card hU
  obtain ⟨m, hm⟩ := hp.index B
  have hmul := B.card_mul_index
  have hBpos : 0 < Nat.card B := Nat.card_pos
  have hidx : B.index ≤ 3 := by
    by_contra hlt
    have : 3 * Nat.card B < B.index * Nat.card B :=
      Nat.mul_lt_mul_of_pos_right (not_le.1 hlt) hBpos
    rw [mul_comm B.index, hmul] at this
    omega
  have hm1 : m ≤ 1 := by
    by_contra hlt
    have : 3 ^ 2 ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) (not_le.1 hlt)
    rw [← hm] at this
    omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hm1 with rfl | rfl
  · have h1 : B.index = 1 := by simpa using hm
    rw [Subgroup.index_eq_one.1 h1]
    exact Subgroup.mem_top _
  · have h3 : B.index = 3 := by simpa using hm
    have hmin : B.index = (Nat.card U).minFac := by
      rw [h3, hU, Nat.Prime.pow_minFac Nat.prime_three (by omega)]
    have : B.Normal := Subgroup.normal_of_index_eq_minFac_card hmin
    have hq : Nat.card (U ⧸ B) = 3 := by rw [← Subgroup.index_eq_card, h3]
    have : IsCyclic (U ⧸ B) := isCyclic_of_prime_card hq
    rw [← QuotientGroup.eq_one_iff]
    have hc : (QuotientGroup.mk ⁅x, y⁆ : U ⧸ B) =
        ⁅(QuotientGroup.mk x : U ⧸ B), (QuotientGroup.mk y : U ⧸ B)⁆ :=
      map_commutatorElement (QuotientGroup.mk' B) x y
    rw [hc, commutatorElement_eq_one_iff_mul_comm]
    exact (IsCyclic.commGroup (α := U ⧸ B)).mul_comm _ _

end CFSG.GH74.GLS.Stage4.Rest.L72
