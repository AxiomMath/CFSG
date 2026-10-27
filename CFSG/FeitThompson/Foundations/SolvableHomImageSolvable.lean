module
public import Mathlib.GroupTheory.Solvable
import CFSG.FeitThompson.Foundations.DerivedSeriesImages

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {G K : Type*} [Group G] [Group K]

theorem isSolvable_range (f : G →* K) [Group.IsSolvable G] : Group.IsSolvable f.range := by
  obtain ⟨r, hr⟩ := Group.IsSolvable.solvable (G := G)
  refine (Group.isSolvable_def _).2 ⟨r, ?_⟩
  rw [derivedSeries_range_eq f r, hr, Subgroup.map_bot, Subgroup.bot_subgroupOf]

theorem isSolvable_map (f : G →* K) (H : Subgroup G) [Group.IsSolvable H] :
    Group.IsSolvable (H.map f) := by
  have := isSolvable_range (f.comp H.subtype)
  rwa [MonoidHom.range_comp, Subgroup.range_subtype] at this

end CFSG.FeitThompson
