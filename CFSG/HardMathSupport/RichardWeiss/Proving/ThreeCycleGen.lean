module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.HardMathSupport.RichardWeiss.Proving

open Equiv Equiv.Perm

theorem closure_threeCycles_alternatingGroup (α : Type*) [Fintype α] [DecidableEq α] :
    Subgroup.closure {x : alternatingGroup α | (x : Perm α).IsThreeCycle} = ⊤ := by
  rw [eq_top_iff]
  intro a _
  have hsub : (alternatingGroup α).subtype '' {x : alternatingGroup α | (x : Perm α).IsThreeCycle}
      = {c : Perm α | c.IsThreeCycle} := by
    ext c
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hc
      exact ⟨⟨c, Equiv.Perm.IsThreeCycle.mem_alternatingGroup hc⟩, hc, rfl⟩
  have hK : (Subgroup.closure {x : alternatingGroup α | (x : Perm α).IsThreeCycle}).map
      (alternatingGroup α).subtype = Subgroup.closure {c : Perm α | c.IsThreeCycle} := by
    rw [MonoidHom.map_closure, hsub]
  have ha : (a : Perm α) ∈ Subgroup.closure {c : Perm α | c.IsThreeCycle} := by
    rw [Equiv.Perm.closure_three_cycles_eq_alternating]
    exact a.2
  rw [← hK] at ha
  exact (Subgroup.mem_map_iff_mem (alternatingGroup α).subtype_injective).1 ha

end CFSG.HardMathSupport.RichardWeiss.Proving

end
