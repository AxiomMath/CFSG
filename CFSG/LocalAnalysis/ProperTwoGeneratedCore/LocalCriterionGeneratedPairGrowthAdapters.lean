module

public import CFSG.Foundations.Basic

public section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

variable {G : Type*} [Group G]

theorem generatedPairGrowth_normalizer_generation_closure
    (J : Subgroup G) (z : G)
    (hgen : Subgroup.normalizer (J : Set G) ⊔ Subgroup.zpowers z = ⊤) :
    Subgroup.closure ((Subgroup.normalizer (J : Set G) : Set G) ∪ {z}) = ⊤ := by
  rw [Subgroup.closure_union, Subgroup.closure_eq, ← Subgroup.zpowers_eq_closure]
  exact hgen

theorem generatedPairGrowth_conjugate_eq_of_normalizes
    (V : Subgroup G) (z : G) (hz : z ∈ Subgroup.normalizer (V : Set G)) :
    CFSG.conjugate V z = V := by
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
    ((Subgroup.normalizer (V : Set G)).inv_mem hz)

end CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
