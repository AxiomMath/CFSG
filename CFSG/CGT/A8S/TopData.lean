module

public import CFSG.CGT.A8S.RelData
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.CGT.A8S

open Equiv Equiv.Perm

namespace Perm8

theorem a8Perm_mem (i : Fin 6) : a8Perm i ∈ alternatingGroup (Fin 8) := by
  rw [mem_alternatingGroup]
  revert i
  decide

theorem transl_mem (c : Fin 8) : transl c ∈ alternatingGroup (Fin 8) := by
  rw [mem_alternatingGroup]
  revert c
  decide

@[expose] def translA (c : Fin 8) : alternatingGroup (Fin 8) := ⟨transl c, transl_mem c⟩

@[simp] theorem coe_translA (c : Fin 8) : (translA c : Perm (Fin 8)) = transl c := rfl

theorem transl_zero : transl 0 = 1 := by decide

theorem exists_transl_mul (c d : Fin 8) : ∃ e : Fin 8, transl c * transl d = transl e := by
  revert c d
  decide

theorem transl_mul_self (c : Fin 8) : transl c * transl c = 1 := by
  revert c
  decide

theorem translA_sq (c : Fin 8) : translA c ^ 2 = 1 :=
  Subtype.ext (by rw [Subgroup.coe_pow, sq]; exact transl_mul_self c)

theorem transl_apply_ne {c : Fin 8} (hc : c ≠ 0) (i : Fin 8) : transl c i ≠ i := by
  revert c i
  decide

theorem a8Perm_two : a8Perm 2 = transl 1 := by decide

theorem a8Perm_three : a8Perm 3 = transl 2 := by decide

theorem a8Perm_four : a8Perm 4 = transl 4 := by decide

theorem transl_eq_prod (c : Fin 8) : transl c =
    a8Perm 2 ^ (c.val % 2) * a8Perm 3 ^ (c.val / 2 % 2) * a8Perm 4 ^ (c.val / 4) := by
  revert c
  decide

@[expose] def wPermA8 (l : List (Fin 6)) : Perm (Fin 8) := (l.map a8Perm).prod

theorem wPermA8_mem (l : List (Fin 6)) : wPermA8 l ∈ alternatingGroup (Fin 8) := by
  unfold wPermA8
  refine list_prod_mem fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact a8Perm_mem i

@[expose] def sqWordA8 : Fin 8 → Fin 8 → List (Fin 6) :=
  ![![[], [], [], [], [], [], [], []],
    ![[], [0, 4], [4, 5, 0, 5], [0, 4, 5, 0, 5], [1, 0, 1, 1, 3], [0, 1, 0, 1, 1, 0, 3],
      [0, 1, 1, 5, 0, 5, 1, 0, 1], [1, 1, 5, 0, 5, 1, 0, 1, 0]],
    ![[], [0, 4], [4, 5, 0, 5], [0, 4, 5, 0, 5], [1, 1, 4, 5, 0, 5, 1],
      [0, 1, 1, 4, 5, 0, 5, 1, 0], [1, 1, 0, 4, 5, 0, 5, 1], [1, 5, 0, 5, 1, 0, 1, 0, 1]],
    ![[], [0, 4], [4, 5, 0, 5], [0, 4, 5, 0, 5], [1, 0, 1, 5, 3, 5, 1],
      [0, 1, 0, 1, 5, 3, 5, 1, 0], [1, 0, 5, 0, 5, 1, 0, 5, 3, 5],
      [5, 0, 5, 1, 0, 1, 0, 1, 1]],
    ![[], [1, 4, 5, 0, 5, 1, 1], [1, 1, 0, 1, 2], [1, 0, 1, 1, 5, 0, 5, 1, 0], [1, 0, 1, 1, 3],
      [0, 1, 0, 1, 1, 0, 3], [1, 1, 0, 4, 5, 0, 5, 1], [5, 0, 5, 1, 0, 1, 0, 1, 1]],
    ![[], [1, 4, 5, 0, 5, 1, 1], [0, 1, 1, 0, 1, 0, 2], [0, 1, 0, 1, 1, 5, 0, 5, 1],
      [1, 0, 1, 1, 3], [0, 1, 0, 1, 1, 0, 3], [1, 0, 5, 0, 5, 1, 0, 5, 3, 5],
      [1, 5, 0, 5, 1, 0, 1, 0, 1]],
    ![[], [0, 1, 5, 3, 5, 1, 1], [1, 1, 0, 1, 2], [0, 1, 0, 1, 1, 5, 0, 5, 1],
      [1, 1, 4, 5, 0, 5, 1], [0, 1, 0, 1, 5, 3, 5, 1, 0], [1, 1, 0, 4, 5, 0, 5, 1],
      [1, 1, 5, 0, 5, 1, 0, 1, 0]],
    ![[], [0, 1, 5, 3, 5, 1, 1], [0, 1, 1, 0, 1, 0, 2], [1, 0, 1, 1, 5, 0, 5, 1, 0],
      [1, 0, 1, 5, 3, 5, 1], [0, 1, 1, 4, 5, 0, 5, 1, 0], [0, 1, 1, 5, 0, 5, 1, 0, 1],
      [1, 1, 5, 0, 5, 1, 0, 1, 0]]]

theorem sqWordA8_spec : ∀ c c' : Fin 8, c ≠ 0 → c' ≠ 0 →
    wPermA8 (sqWordA8 c c') * transl c = transl c * wPermA8 (sqWordA8 c c') ∧
      wPermA8 (sqWordA8 c c') * wPermA8 (sqWordA8 c c') = transl c' := by
  decide

theorem exists_sq_eq_translA {c c' : Fin 8} (hc : c ≠ 0) (hc' : c' ≠ 0) :
    ∃ s : alternatingGroup (Fin 8), s * translA c = translA c * s ∧ s ^ 2 = translA c' := by
  obtain ⟨h1, h2⟩ := sqWordA8_spec c c' hc hc'
  exact ⟨⟨_, wPermA8_mem (sqWordA8 c c')⟩, Subtype.ext h1, Subtype.ext (by
    rw [Subgroup.coe_pow, sq]
    exact h2)⟩

end Perm8

end CFSG.CGT.A8S
