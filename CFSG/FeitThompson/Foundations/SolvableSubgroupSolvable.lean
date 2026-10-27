module

public import Mathlib.GroupTheory.Solvable
import CFSG.FeitThompson.Foundations.SubgroupDerivedSeriesLe

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {G : Type*} [Group G]

theorem isSolvable_of_le {H K : Subgroup G} (h : H ≤ K) [Group.IsSolvable K] :
    Group.IsSolvable H := by
  obtain ⟨r, hr⟩ := Group.IsSolvable.solvable (G := K)
  refine (Group.isSolvable_def H).2 ⟨r, ?_⟩
  have hmap : (derivedSeries H r).map H.subtype = ⊥ :=
    le_bot_iff.1 <| (map_derivedSeries_subtype_mono h r).trans_eq (by rw [hr, Subgroup.map_bot])
  exact (Subgroup.map_eq_bot_iff_of_injective (H := derivedSeries H r)
    H.subtype_injective).1 hmap

end CFSG.FeitThompson

