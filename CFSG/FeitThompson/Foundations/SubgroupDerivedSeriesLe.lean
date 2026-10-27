module

public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Foundations.CommutatorMonotone

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {G : Type*} [Group G]

theorem map_derivedSeries_subtype_le (H : Subgroup G) (n : ℕ) :
    (derivedSeries H n).map H.subtype ≤ derivedSeries G n :=
  map_derivedSeries_le_derivedSeries H.subtype n

theorem map_derivedSeries_subtype_mono {H K : Subgroup G} (h : H ≤ K) (n : ℕ) :
    (derivedSeries H n).map H.subtype ≤ (derivedSeries K n).map K.subtype := by
  rw [← Subgroup.subtype_comp_inclusion h, ← Subgroup.map_map]
  exact Subgroup.map_mono (map_derivedSeries_le_derivedSeries _ n)

theorem derivedSeries_succ_le (n : ℕ) : derivedSeries G (n + 1) ≤ derivedSeries G n :=
  derivedSeries_antitone G (Nat.le_succ n)

end CFSG.FeitThompson
