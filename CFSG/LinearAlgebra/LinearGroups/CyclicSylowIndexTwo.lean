module

public import CFSG.LinearAlgebra.LinearGroups.RegularPermutationSign
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LinearGroups

open Equiv

theorem cyclic_sylow_index_two {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (hG : Even (Fintype.card G)) (S : Sylow 2 G) (hS : IsCyclic S) :
    let ε : G →* ℤˣ := Perm.sign.comp (MulAction.toPermHom G G)
    (∀ g, ε g = Perm.sign (Equiv.mulLeft g)) ∧ Function.Surjective ε ∧ ε.ker.Normal ∧
      ε.ker.index = 2 := by
  intro ε
  have hε : ∀ g, ε g = Perm.sign (Equiv.mulLeft g) := fun g => rfl
  obtain ⟨g, hg⟩ := hS.exists_generator
  have hord : orderOf (g : G) = Nat.card S := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_card_of_forall_mem_zpowers hg
  have hcard : Fintype.card G = Nat.card S * (S : Subgroup G).index := by
    rw [← Nat.card_eq_fintype_card]
    exact (Subgroup.card_mul_index (S : Subgroup G)).symm
  have hpos : 0 < Nat.card S := Nat.card_pos
  have hdiv : Fintype.card G / orderOf (g : G) = (S : Subgroup G).index := by
    rw [hord, hcard, Nat.mul_div_cancel_left _ hpos]
  have hsign : ε g = -1 := by
    rw [hε, (regular_permutation_sign (g : G)).2.2, hdiv]
    have hle : (S : Subgroup G).index ≤ Fintype.card G := by
      rw [hcard]
      exact Nat.le_mul_of_pos_left _ hpos
    obtain ⟨a, ha⟩ := hG
    obtain ⟨b, hb⟩ : Odd (S : Subgroup G).index :=
      Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp S.not_dvd_index)
    have hodd : Odd (Fintype.card G - (S : Subgroup G).index) := ⟨a - b - 1, by omega⟩
    exact hodd.neg_one_pow
  have hsurj : Function.Surjective ε := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, map_one ε⟩
    · exact ⟨g, hsign⟩
  refine ⟨hε, hsurj, inferInstance, ?_⟩
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top,
    Nat.card_eq_fintype_card, Fintype.card_units_int]

end CFSG.LinearGroups
