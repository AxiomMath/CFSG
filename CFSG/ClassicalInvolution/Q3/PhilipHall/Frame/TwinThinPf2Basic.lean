module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPfModel
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.Perm.List
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf

@[expose] def pc {n : ℕ} (cs : List (List (Fin n))) : Equiv.Perm (Fin n) :=
  (cs.map List.formPerm).prod

section Words

variable {G : Type*} [Group G]

@[expose] def letter (gs : List G) (l : ℕ) : G :=
  if l < gs.length then gs.getD l 1 else (gs.getD (l - gs.length) 1)⁻¹

@[expose] def evalW (gs : List G) (w : List ℕ) : G := (w.map (letter gs)).prod

variable {G' : Type*} [Group G']

theorem map_letter (f : G →* G') (gs : List G) (l : ℕ) :
    f (letter gs l) = letter (gs.map f) l := by
  unfold letter
  simp only [List.length_map]
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD]
    rcases Nat.lt_or_ge (l - gs.length) gs.length with h' | h'
    · simp [h']
    · simp [Nat.not_lt.mpr h']

theorem map_evalW (f : G →* G') (gs : List G) (w : List ℕ) :
    f (evalW gs w) = evalW (gs.map f) w := by
  unfold evalW
  rw [map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun l _ => map_letter f gs l

theorem letter_mem_closure (gs : List G) (l : ℕ) :
    letter gs l ∈ Subgroup.closure {x | x ∈ gs} := by
  unfold letter
  split_ifs with h
  · have : gs.getD l 1 ∈ gs := by
      simpa [List.getD_eq_getElem?_getD, h] using List.getElem_mem h
    exact Subgroup.subset_closure this
  · by_cases h' : l - gs.length < gs.length
    · have : gs.getD (l - gs.length) 1 ∈ gs := by
        simpa [List.getD_eq_getElem?_getD, h'] using List.getElem_mem h'
      exact (Subgroup.closure _).inv_mem (Subgroup.subset_closure this)
    · simp [List.getD_eq_getElem?_getD, Nat.not_lt.mp h']

theorem evalW_mem_closure (gs : List G) (w : List ℕ) :
    evalW gs w ∈ Subgroup.closure {x | x ∈ gs} := by
  unfold evalW
  exact Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx
    exact letter_mem_closure gs l

end Words

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf
