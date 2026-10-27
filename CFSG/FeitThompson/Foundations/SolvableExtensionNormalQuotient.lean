module

public import Mathlib.GroupTheory.Solvable
import CFSG.FeitThompson.Foundations.DerivedSeriesShift
import CFSG.FeitThompson.Foundations.SubgroupDerivedSeriesLe

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {G : Type*} [Group G]

theorem derivedSeries_le_of_derivedSeries_quotient_eq_bot (N : Subgroup G) [N.Normal] {s : ℕ}
    (hs : derivedSeries (G ⧸ N) s = ⊥) : derivedSeries G s ≤ N := by
  rw [← QuotientGroup.ker_mk' N, ← Subgroup.map_eq_bot_iff,
    map_derivedSeries_eq (QuotientGroup.mk'_surjective N) s]
  exact hs

theorem derivedSeries_add_eq_bot (N : Subgroup G) [N.Normal] {r s : ℕ}
    (hr : derivedSeries N r = ⊥) (hs : derivedSeries (G ⧸ N) s = ⊥) :
    derivedSeries G (r + s) = ⊥ := by
  have hle : derivedSeries G s ≤ N :=
    derivedSeries_le_of_derivedSeries_quotient_eq_bot N hs
  have h := map_derivedSeries_subtype_mono hle r
  rw [hr, Subgroup.map_bot] at h
  rw [add_comm, ← map_subtype_derivedSeries_derivedSeries G s r]
  exact le_bot_iff.mp h

theorem isSolvable_of_normal_of_quotient (N : Subgroup G) [N.Normal] [Group.IsSolvable N]
    [Group.IsSolvable (G ⧸ N)] : Group.IsSolvable G := by
  obtain ⟨r, hr⟩ := Group.IsSolvable.solvable (G := N)
  obtain ⟨s, hs⟩ := Group.IsSolvable.solvable (G := G ⧸ N)
  exact (Group.isSolvable_def G).2 ⟨r + s, derivedSeries_add_eq_bot N hr hs⟩

end CFSG.FeitThompson

