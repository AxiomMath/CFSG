module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.ComponentClassification.Helpers

public section

namespace CFSG.Assembly.ComponentType

theorem oddCore_eq_bot_of_involution (G : Type*) [Group G] [Finite G] [IsSimpleGroup G]
    (t : G) (ht : orderOf t = 2) : oddCore G = ⊥ := by
  exact CFSG.ComponentClassification.Helpers.oddCore_eq_bot_of_involution G t ht

theorem oddCore_eq_bot_of_componentType (G : Type*) [Group G] [Finite G] [IsSimpleGroup G]
    (hcomp : IsComponentType G) : oddCore G = ⊥ := by
  obtain ⟨t, ht, _⟩ := hcomp
  exact oddCore_eq_bot_of_involution G t ht

end CFSG.Assembly.ComponentType
