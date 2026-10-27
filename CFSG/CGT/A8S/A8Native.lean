module

public import CFSG.CGT.A8S.RelData
public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCoverPerm

public section

namespace CFSG.CGT.A8S

open Equiv Equiv.Perm CFSG.LocalAnalysis.ComponentInitial

@[expose] def permWA8 : A8Word → Perm (Fin 8)
  | [] => 1
  | (i, b) :: w => (if b then a8Perm i else (a8Perm i)⁻¹) * permWA8 w

theorem evalA8_a8Perm (w : A8Word) : evalA8 a8Perm w = permWA8 w := by
  induction w with
  | nil => rw [evalA8_nil]; rfl
  | cons l w ih =>
    obtain ⟨i, b⟩ := l
    rw [evalA8_cons, ih]
    rfl

theorem permWA8_a8Rels : ∀ r ∈ a8Rels, permWA8 r = 1 := by
  decide +kernel

theorem evalA8_a8Perm_eq_one {r : A8Word} (hr : r ∈ a8Rels) : evalA8 a8Perm r = 1 := by
  rw [evalA8_a8Perm, permWA8_a8Rels r hr]

theorem sign_a8Perm : ∀ i, sign (a8Perm i) = 1 := by
  decide +kernel

@[expose] def a8Alt (i : Fin 6) : alternatingGroup (Fin 8) :=
  ⟨a8Perm i, mem_alternatingGroup.2 (sign_a8Perm i)⟩

@[simp] theorem coe_a8Alt (i : Fin 6) : ((a8Alt i : alternatingGroup (Fin 8)) : Perm (Fin 8)) =
    a8Perm i :=
  rfl

theorem coe_evalA8_a8Alt (w : A8Word) :
    ((evalA8 a8Alt w : alternatingGroup (Fin 8)) : Perm (Fin 8)) = evalA8 a8Perm w := by
  induction w with
  | nil => simp
  | cons l w ih =>
    obtain ⟨i, b⟩ := l
    cases b <;> simp [ih]

theorem evalA8_a8Alt_eq_one {r : A8Word} (hr : r ∈ a8Rels) : evalA8 a8Alt r = 1 :=
  Subtype.ext ((coe_evalA8_a8Alt r).trans (evalA8_a8Perm_eq_one hr))

@[expose] def a8ThreeCycleWord : Fin 6 → List (Fin 6) :=
  ![[0, 1, 5, 0, 5, 1, 0, 1, 5, 4], [1, 5, 1, 1, 3, 5, 1, 5, 4], [1, 5, 1, 2, 5, 1, 1, 3, 5],
    [0, 4, 5, 1, 4, 0, 5, 1, 2], [1, 3, 5, 1, 5, 0, 1, 2, 5, 1], [1, 1, 5, 1, 5, 1, 2, 5, 4]]

theorem altThreeCyclePerm_eq_prod :
    ∀ k : Fin 6, altThreeCyclePerm k = ((a8ThreeCycleWord k).map a8Perm).prod := by
  decide +kernel

theorem closure_range_a8Perm : Subgroup.closure (Set.range a8Perm) = alternatingGroup (Fin 8) := by
  refine le_antisymm ((Subgroup.closure_le _).2 ?_) ?_
  · rintro _ ⟨i, rfl⟩
    exact mem_alternatingGroup.2 (sign_a8Perm i)
  · rw [← closure_altThreeCyclePerm (n := 6), Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe, altThreeCyclePerm_eq_prod k]
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
    exact Subgroup.subset_closure ⟨j, rfl⟩

end CFSG.CGT.A8S
