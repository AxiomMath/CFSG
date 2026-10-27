module

public import CFSG.LocalAnalysis.ComponentClassification.GS82HDefs

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

theorem not_catalog_of_not_uOutcome (hUc : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) : ¬ Blueprint.Catalog X := by
  intro hcat
  obtain ⟨-, -, -, -, htop⟩ := SmallLocal.simple_generalized_fitting_self_local X hnonab
  let e : GeneralizedFitting.subgroup X ≃* X := (MulEquiv.subgroupCongr htop).trans topEquiv
  have hs : IsSimpleGroup (GeneralizedFitting.subgroup X) := e.isSimpleGroup
  have hn : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    refine ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective ?_)⟩
    rw [map_mul, map_mul]
    exact h
  exact hU (hUc X hs hn (SectionRank.catalog_of_mulEquiv e hcat) hz)

namespace Eight2

theorem CtxA0.gs82HAmbient {X : Type} [Group X] [Finite X] (c : CtxA0 X)
    (hUc : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) : GS82HAmbient X := by
  have := c.s.isSimpleGroup
  exact ⟨c.s.isSimpleGroup, c.s.nonab, c.s.kProper,
    not_catalog_of_not_uOutcome hUc c.s.nonab c.s.unbal c.s.notU, c.s.unbal, c.s.notU⟩

end Eight2

end CFSG.ComponentClassification.GSThmB
