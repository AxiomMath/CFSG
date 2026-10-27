module
public import Mathlib.GroupTheory.Solvable
import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {G K : Type*} [Group G] [Group K]

theorem derivedSeries_succ_eq_closure (n : ℕ) :
    derivedSeries G (n + 1) =
      Subgroup.closure {g : G | ∃ a ∈ derivedSeries G n, ∃ b ∈ derivedSeries G n,
        a⁻¹ * b⁻¹ * a * b = g} := by
  rw [derivedSeries_succ, closure_setOf_inv_mul_inv_mul_mul]

theorem map_derivedSeries_eq_derivedSeries_range (f : G →* K) (n : ℕ) :
    (derivedSeries G n).map f = (derivedSeries f.range n).map f.range.subtype := by
  rw [← map_derivedSeries_eq f.rangeRestrict_surjective n, Subgroup.map_map,
    MonoidHom.subtype_comp_rangeRestrict]

theorem derivedSeries_range_eq (f : G →* K) (n : ℕ) :
    derivedSeries f.range n = ((derivedSeries G n).map f).subgroupOf f.range := by
  rw [Subgroup.subgroupOf, map_derivedSeries_eq_derivedSeries_range f n,
    Subgroup.comap_map_eq_self_of_injective f.range.subtype_injective]

end CFSG.FeitThompson
