module

public import Mathlib.Order.SupIndep
public import Mathlib.Algebra.Group.Subgroup.Ker

public section

namespace CFSG.GroupTheory

variable {G : Type*} [Group G]

open Classical in
theorem supIndep_image_subgroupOf {X : Subgroup G} {s : Finset (Subgroup G)}
    (hs : s.SupIndep id) : (s.image fun W => W.subgroupOf X).SupIndep id := by
  classical
  refine Finset.SupIndep.image ?_
  intro t ht W hW hWt
  have hd : Disjoint W (t.sup id) := hs ht hW hWt
  rw [Subgroup.disjoint_def] at hd ⊢
  intro x hx1 hx2
  have hle : t.sup (id ∘ fun W : Subgroup G => W.subgroupOf X) ≤ (t.sup id).subgroupOf X :=
    Finset.sup_le fun W' hW' y hy =>
      Subgroup.mem_subgroupOf.mpr (Finset.le_sup (f := id) hW' (Subgroup.mem_subgroupOf.mp hy))
  exact Subtype.ext (hd (Subgroup.mem_subgroupOf.mp hx1) (Subgroup.mem_subgroupOf.mp (hle hx2)))

open Classical in
theorem sup_image_subgroupOf {X : Subgroup G} (s : Finset (Subgroup G))
    (hsX : ∀ W ∈ s, W ≤ X) :
    (s.image fun W => W.subgroupOf X).sup id = (s.sup id).subgroupOf X := by
  classical
  rw [Finset.sup_image]
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sup_insert, Finset.sup_insert,
      ih (fun W hW => hsX W (Finset.mem_insert_of_mem hW))]
    exact (Subgroup.subgroupOf_sup (hsX a (Finset.mem_insert_self a s))
      (Finset.sup_le fun W hW => hsX W (Finset.mem_insert_of_mem hW))).symm

end CFSG.GroupTheory
