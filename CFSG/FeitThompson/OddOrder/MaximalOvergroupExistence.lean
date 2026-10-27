module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.SetLike.Fintype
public import Mathlib.Order.Atoms

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {G : Type*} [Group G]

theorem isCoatom_iff_ne_top_and_forall_not_lt_lt {M : Subgroup G} :
    IsCoatom M ↔ M ≠ ⊤ ∧ ∀ K : Subgroup G, ¬(M < K ∧ K < ⊤) := by
  constructor
  · exact fun ⟨hne, hmax⟩ => ⟨hne, fun _ ⟨hMK, hKtop⟩ => hKtop.ne (hmax _ hMK)⟩
  · refine fun ⟨hne, h⟩ => ⟨hne, fun K hMK => ?_⟩
    by_contra hK
    exact h K ⟨hMK, lt_top_iff_ne_top.2 hK⟩

variable [Finite G]

theorem exists_isCoatom_ge_of_ne_top {H : Subgroup G} (hH : H ≠ ⊤) :
    ∃ M : Subgroup G, IsCoatom M ∧ H ≤ M :=
  (IsCoatomic.eq_top_or_exists_le_coatom H).resolve_left hH

theorem exists_maximal_subgroup_ge_of_ne_top {H : Subgroup G} (hH : H ≠ ⊤) :
    ∃ M : Subgroup G, H ≤ M ∧ M ≠ ⊤ ∧ ∀ K : Subgroup G, ¬(M < K ∧ K < ⊤) := by
  obtain ⟨M, hM, hHM⟩ := exists_isCoatom_ge_of_ne_top hH
  obtain ⟨hne, hmax⟩ := isCoatom_iff_ne_top_and_forall_not_lt_lt.1 hM
  exact ⟨M, hHM, hne, hmax⟩

theorem exists_maximal_subgroup_ge_of_lt_top {H : Subgroup G} (hH : H < ⊤) :
    ∃ M : Subgroup G, H ≤ M ∧ M ≠ ⊤ ∧ ∀ K : Subgroup G, ¬(M < K ∧ K < ⊤) :=
  exists_maximal_subgroup_ge_of_ne_top hH.ne

end CFSG.FeitThompson
