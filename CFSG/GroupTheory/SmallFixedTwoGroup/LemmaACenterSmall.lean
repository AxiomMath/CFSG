module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GroupTheory.SmallFixedTwoGroup

open Subgroup

theorem card_center_le_two_of_not_commutative {B : Type*} [Group B] [Finite B]
    (hcard : Nat.card B ≤ 8) (hnc : ¬ ∀ a b : B, a * b = b * a) :
    Nat.card (center B) ≤ 2 := by
  by_contra hle
  rw [not_le] at hle
  have hZ : 3 ≤ Nat.card (center B) := by omega
  have hmul : Nat.card (center B) * (center B).index = Nat.card B :=
    Subgroup.card_mul_index (center B)
  have hIndex : (center B).index ≤ 2 := by
    by_contra h
    rw [not_le] at h
    have h3 : 3 ≤ (center B).index := by omega
    have hmul3 : 3 * 3 ≤ Nat.card (center B) * (center B).index :=
      Nat.mul_le_mul hZ h3
    omega
  have hdvd : (center B).index ∣ 2 := by
    have hpos : (center B).index ≠ 0 := FiniteIndex.index_ne_zero
    have hcases : (center B).index = 1 ∨ (center B).index = 2 := by omega
    rcases hcases with h | h <;> simp [h]
  have hcyc : IsCyclic (B ⧸ center B) := by
    apply isCyclic_of_card_dvd_prime (p := 2)
    rw [← Subgroup.index_eq_card]
    exact hdvd
  letI : IsCyclic (B ⧸ center B) := hcyc
  letI : CommGroup B :=
    commGroupOfCyclicCenterQuotient (QuotientGroup.mk' (center B))
      (QuotientGroup.ker_mk' (center B)).le
  exact hnc fun a b => mul_comm a b

end CFSG.GroupTheory.SmallFixedTwoGroup
