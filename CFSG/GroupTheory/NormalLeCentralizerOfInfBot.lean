module

public import Mathlib.GroupTheory.Subgroup.Centralizer

public section

namespace CFSG

theorem normal_le_centralizer_of_inf_eq_bot {X : Type} [Group X] {M K : Subgroup X}
    (hM : M.Normal) (hK : K.Normal) (h : M ⊓ K = ⊥) :
    M ≤ Subgroup.centralizer (K : Set X) := by
  intro m hm
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact (Subgroup.commute_of_normal_of_disjoint M K hM hK (disjoint_iff.mpr h) m k hm hk).symm.eq

end CFSG

end
