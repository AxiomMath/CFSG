module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix

open Equiv

@[expose] def xPermutation : Perm (Fin 6) := swap 0 1 * swap 1 2

@[expose] def yPermutation : Perm (Fin 6) :=
  swap 1 2 * swap 2 3 * swap 3 4 * swap 4 5

theorem x_even : xPermutation.sign = 1 := by decide +kernel

theorem y_even : yPermutation.sign = 1 := by decide +kernel

@[expose] def x : alternatingGroup (Fin 6) :=
  ⟨xPermutation, Perm.mem_alternatingGroup.mpr x_even⟩

@[expose] def y : alternatingGroup (Fin 6) :=
  ⟨yPermutation, Perm.mem_alternatingGroup.mpr y_even⟩

private def letter (i : Fin 4) : alternatingGroup (Fin 6) := ![x, y, x⁻¹, y⁻¹] i

private def wordValue (word : List (Fin 4)) : alternatingGroup (Fin 6) :=
  (word.map letter).prod

private def threeCycleWords : List (List (Fin 4)) :=
  [ [1, 2, 3, 2, 1],
    [3, 0, 1, 0, 3],
    [2, 3, 2, 1, 1],
    [0, 3, 0, 1, 1, 0, 3],
    [3, 3, 0, 1, 0],
    [0, 1, 1, 2, 3, 0],
    [1, 1, 0, 1, 2, 1, 0],
    [1, 2, 3, 0, 3, 2],
    [0, 1, 0, 3],
    [0, 1, 1, 0, 3, 0, 3],
    [3, 0, 1, 0],
    [1, 2, 3, 2],
    [0, 3, 2, 1, 1, 0],
    [3, 0, 1, 1, 0, 3, 0],
    [1, 0, 1, 2, 1, 0, 1],
    [2, 3, 0, 3, 2, 1],
    [1, 1, 2, 3, 2],
    [2, 3, 2, 1],
    [0, 1, 2, 1, 0, 1, 1],
    [0, 1, 0, 3, 3],
    [0],
    [1, 0, 3, 0],
    [3, 3, 2, 1, 2, 1],
    [3, 2, 1],
    [2],
    [1, 0, 3],
    [1, 1, 0, 3, 0, 3],
    [3, 2, 1, 2],
    [2, 1, 2, 3],
    [1, 2, 3],
    [1, 1, 0, 3, 3],
    [2, 3, 3, 2, 3, 0, 3],
    [3, 0, 3, 0, 1, 1],
    [1, 2, 1, 2, 3, 3],
    [0, 3, 3, 0, 1],
    [2, 1, 1, 2, 3],
    [3, 0, 1],
    [0, 3, 0, 1],
    [0, 1, 1, 0, 1, 2, 1],
    [1, 0, 3, 3, 0] ]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem threeCycleWords_cover :
    ∀ permutation : Perm (Fin 6), permutation.support.card = 3 →
      ∃ word ∈ threeCycleWords, (wordValue word : Perm (Fin 6)) = permutation := by
  decide +kernel

private theorem wordValue_mem_closure (word : List (Fin 4)) :
    wordValue word ∈ Subgroup.closure ({x, y} : Set (alternatingGroup (Fin 6))) := by
  let closure := Subgroup.closure ({x, y} : Set (alternatingGroup (Fin 6)))
  have hx : x ∈ closure := Subgroup.subset_closure (by simp)
  have hy : y ∈ closure := Subgroup.subset_closure (by simp)
  have hletter : ∀ i, letter i ∈ closure := by
    intro i
    fin_cases i
    · simpa [letter] using hx
    · simpa [letter] using hy
    · simpa [letter] using closure.inv_mem hx
    · simpa [letter] using closure.inv_mem hy
  induction word with
  | nil => exact closure.one_mem
  | cons i word inductionHypothesis =>
    exact closure.mul_mem (hletter i) inductionHypothesis

theorem generating_pair :
    Subgroup.closure ({x, y} : Set (alternatingGroup (Fin 6))) = ⊤ := by
  apply top_unique
  rw [← alternatingGroup.closure_isThreeCycles_eq_top (α := Fin 6)]
  apply (Subgroup.closure_le _).mpr
  intro permutation hpermutation
  obtain ⟨word, _, hword⟩ :=
    threeCycleWords_cover permutation (Perm.IsThreeCycle.card_support hpermutation)
  have heq : wordValue word = permutation := Subtype.ext hword
  rw [← heq]
  exact wordValue_mem_closure word

theorem card_alternating_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem x_order : orderOf x = 3 := by
  have hx : x ^ 3 = 1 ∧ x ≠ 1 := by decide +kernel
  exact orderOf_eq_prime hx.1 hx.2

theorem y_order : orderOf y = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hy : y ^ 5 = 1 ∧ y ≠ 1 := by decide +kernel
  exact orderOf_eq_prime hy.1 hy.2

theorem xy_order : orderOf (x * y) = 4 := by
  have hxy : (x * y) ^ 4 = 1 ∧ (x * y) ^ 2 ≠ 1 := by decide +kernel
  exact orderOf_eq_prime_pow (p := 2) (n := 1) hxy.2 hxy.1

theorem commutator_order : orderOf (x * y * x⁻¹ * y⁻¹) = 2 := by
  have hcommutator : (x * y * x⁻¹ * y⁻¹) ^ 2 = 1 ∧ x * y * x⁻¹ * y⁻¹ ≠ 1 := by
    decide +kernel
  exact orderOf_eq_prime hcommutator.1 hcommutator.2

theorem generating_pair_word_orders :
    (orderOf x, orderOf y, orderOf (x * y), orderOf (x * y * x⁻¹ * y⁻¹)) = (3, 5, 4, 2) := by
  rw [x_order, y_order, xy_order, commutator_order]

end CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix
