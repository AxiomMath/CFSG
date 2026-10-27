module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Defs

public section

namespace CFSG.OddStandard.HigherRank.G2Three

open Subgroup CFSG.Open
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G} {K : Subgroup G}

private theorem eq_of_orderOf_eq_two_of_isCyclic' {Z : Type*} [Group Z] [Finite Z] [IsCyclic Z]
    {a b : Z} (ha : orderOf a = 2) (hb : orderOf b = 2) : a = b := by
  classical
  have := Fintype.ofFinite Z
  by_contra hab
  have h := IsCyclic.card_pow_eq_one_le (α := Z) (n := 2) (by norm_num)
  have hsub : ({1, a, b} : Finset Z) ⊆ Finset.univ.filter (fun x : Z => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · simp
    · rw [← ha]; exact pow_orderOf_eq_one x
    · rw [← hb]; exact pow_orderOf_eq_one x
  have ha1 : a ≠ 1 := by intro h; rw [h, orderOf_one] at ha; norm_num at ha
  have hb1 : b ≠ 1 := by intro h; rw [h, orderOf_one] at hb; norm_num at hb
  have hcard : ({1, a, b} : Finset Z).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using hab
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm ha1, Ne.symm hb1⟩
  have := Finset.card_le_card hsub
  omega

end CFSG.OddStandard.HigherRank.G2Three
