module

public import CFSG.GroupTheory.OddOrderClosure
public import CFSG.Assembly.Defs

public section

namespace CFSG.GroupTheory

open Subgroup

theorem normalClosure_eq_closure_of_conj_invariant {G : Type*} [Group G] {s : Set G}
    (hs : ∀ g x : G, x ∈ s → g * x * g⁻¹ ∈ s) :
    Subgroup.normalClosure s = Subgroup.closure s := by
  rw [Subgroup.normalClosure]
  congr 1
  exact Set.Subset.antisymm
    (fun x hx => by
      obtain ⟨a, ha, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
      obtain ⟨g, rfl⟩ := isConj_iff.mp hconj
      exact hs g a ha)
    Group.subset_conjugatesOfSet

variable {G : Type*} [Group G]

end CFSG.GroupTheory
