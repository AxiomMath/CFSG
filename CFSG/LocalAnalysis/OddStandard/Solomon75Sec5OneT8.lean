module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Data.List.GetD

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm

@[expose] def T8gens : List (Perm (Fin 8)) :=
  [swap 0 1 * swap 2 3, swap 0 1 * swap 4 5, swap 0 1 * swap 6 7,
   swap 2 3 * swap 4 5, swap 2 3 * swap 6 7, swap 4 5 * swap 6 7,
   swap 0 2 * swap 1 3 * swap 4 6 * swap 5 7, swap 0 4 * swap 1 5 * swap 2 6 * swap 3 7]

@[expose] def T8 : Subgroup (Perm (Fin 8)) := Subgroup.closure {g | g ∈ T8gens}

def T8word (w : List ℕ) : Perm (Fin 8) := (w.map fun i => T8gens.getD i 1).prod

def T8words : List (List ℕ) :=
  [[], [0], [1], [2], [3], [4], [5], [6], [7], [5, 0], [6, 0], [6, 1], [6, 2], [6, 3], [6, 4],
   [6, 5], [7, 0], [7, 1], [7, 2], [7, 3], [7, 4], [7, 5], [7, 6], [6, 5, 0], [7, 5, 0],
   [7, 6, 0], [7, 6, 1], [7, 6, 2], [7, 6, 3], [7, 6, 4], [7, 6, 5], [7, 6, 5, 0]]

def T8S : Finset (Perm (Fin 8)) := (T8words.map T8word).toFinset

section T8Compute

attribute [-instance] Fintype.decidableForallFintype

theorem T8S_card : T8S.card = 32 := by decide +kernel

theorem T8S_one : (1 : Perm (Fin 8)) ∈ T8S := by decide +kernel

theorem T8S_left : ∀ g ∈ T8gens, ∀ y ∈ T8S, g * y ∈ T8S := by decide +kernel

theorem T8gens_sq : ∀ g ∈ T8gens, g * g = 1 := by decide +kernel

def T8Z : Finset (Perm (Fin 8)) := T8S.filter fun t => ∀ g ∈ T8gens, t * g = g * t

theorem mem_T8Z {x : Perm (Fin 8)} : x ∈ T8Z ↔ x ∈ T8S ∧ ∀ g ∈ T8gens, x * g = g * x :=
  Finset.mem_filter

theorem T8Z_card : T8Z.card = 2 := by decide +kernel

def T8inv : List (Perm (Fin 8)) :=
  [swap 0 5 * swap 1 4 * swap 2 6 * swap 3 7, swap 0 3 * swap 1 2 * swap 4 7 * swap 5 6,
   swap 0 4 * swap 1 5 * swap 2 6 * swap 3 7, swap 0 7 * swap 1 6 * swap 2 4 * swap 3 5]

def T8invWord (w : List ℕ) : Perm (Fin 8) := (w.map fun i => T8inv.getD i 1).prod

def T8genWords : List (List ℕ) :=
  [[3, 1, 0], [2, 0], [2, 3, 1], [3, 2, 1], [3, 2, 3, 0], [1, 3, 0], [0, 1, 0], [2]]

theorem T8gens_eq : T8gens = T8genWords.map T8invWord := by decide +kernel

theorem T8inv_mem : ∀ g ∈ T8inv, g ∈ T8S := by decide +kernel

theorem T8inv_sq : ∀ g ∈ T8inv, g * g = 1 := by decide +kernel

theorem T8inv_support : ∀ g ∈ T8inv, g.support.card = 8 := by decide +kernel

end T8Compute

theorem T8word_mem (w : List ℕ) : T8word w ∈ T8 := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  by_cases h : i < T8gens.length
  · rw [List.getD_eq_getElem _ _ h]
    exact Subgroup.subset_closure (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (not_lt.1 h)]
    exact T8.one_mem

theorem mem_T8_of_mem_T8S {x : Perm (Fin 8)} (hx : x ∈ T8S) : x ∈ T8 := by
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hx)
  exact T8word_mem w

theorem mem_T8S_of_mem_T8 {x : Perm (Fin 8)} (hx : x ∈ T8) : x ∈ T8S := by
  change x ∈ Subgroup.closure {g | g ∈ T8gens} at hx
  induction hx using Subgroup.closure_induction_left with
  | one => exact T8S_one
  | mul_left g hg y _ hy => exact T8S_left g hg y hy
  | inv_mul_cancel g hg y _ hy =>
    rw [inv_eq_of_mul_eq_one_right (T8gens_sq g hg)]
    exact T8S_left g hg y hy

theorem mem_T8_iff {x : Perm (Fin 8)} : x ∈ T8 ↔ x ∈ T8S :=
  ⟨mem_T8S_of_mem_T8, mem_T8_of_mem_T8S⟩

theorem T8_card : Nat.card T8 = 32 := by
  have e : T8 ≃ T8S := Equiv.subtypeEquivRight fun x => mem_T8_iff
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  exact T8S_card

theorem T8_le_alternatingGroup : T8 ≤ alternatingGroup (Fin 8) := by
  refine (Subgroup.closure_le _).2 fun g hg => ?_
  have hg' : g ∈ T8gens := hg
  rw [SetLike.mem_coe, mem_alternatingGroup]
  simp only [T8gens, List.mem_cons, List.not_mem_nil, or_false] at hg'
  rcases hg' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Perm.sign_mul, Perm.sign_swap']

theorem mem_T8Z_iff {x : Perm (Fin 8)} : x ∈ T8Z ↔ x ∈ T8 ∧ ∀ y ∈ T8, x * y = y * x := by
  constructor
  · intro hx
    rw [mem_T8Z] at hx
    refine ⟨mem_T8_of_mem_T8S hx.1, fun y hy => ?_⟩
    have hle : T8 ≤ Subgroup.centralizer {x} := by
      refine (Subgroup.closure_le _).2 fun g hg => ?_
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.1 hh]
      exact hx.2 g hg
    exact Subgroup.mem_centralizer_iff.1 (hle hy) x rfl
  · rintro ⟨hx, h⟩
    rw [mem_T8Z]
    exact ⟨mem_T8S_of_mem_T8 hx, fun g hg => h g (Subgroup.subset_closure hg)⟩

theorem T8_center_card : Nat.card (Subgroup.center T8) = 2 := by
  have e : Subgroup.center T8 ≃ T8Z :=
    { toFun := fun z => ⟨z.1.1, mem_T8Z_iff.2 ⟨z.1.2, fun y hy => by
        have h := Subgroup.mem_center_iff.1 z.2 ⟨y, hy⟩
        exact (congrArg Subtype.val h).symm⟩⟩
      invFun := fun x => ⟨⟨x.1, (mem_T8Z_iff.1 x.2).1⟩, by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext ((mem_T8Z_iff.1 x.2).2 g.1 g.2).symm⟩
      left_inv := fun z => rfl
      right_inv := fun x => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  exact T8Z_card

theorem T8_eq_closure_involutions :
    T8 = Subgroup.closure {t : Perm (Fin 8) | t ∈ T8 ∧ t * t = 1 ∧ t.support.card = 8} := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 fun g hg => ?_
    have hg' : g ∈ T8gens := hg
    rw [T8gens_eq] at hg'
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg'
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    by_cases h : i < T8inv.length
    · rw [List.getD_eq_getElem _ _ h]
      have hmem : T8inv[i] ∈ T8inv := List.getElem_mem h
      exact Subgroup.subset_closure
        ⟨mem_T8_of_mem_T8S (T8inv_mem _ hmem), T8inv_sq _ hmem, T8inv_support _ hmem⟩
    · rw [List.getD_eq_default _ _ (not_lt.1 h)]
      exact one_mem _
  · exact (Subgroup.closure_le _).2 fun t ht => ht.1

theorem swap_mul_swap_mem_T8 : swap 0 1 * swap 2 3 ∈ T8 :=
  Subgroup.subset_closure (by simp [T8gens])

end CFSG.OddStandard.Solomon75
