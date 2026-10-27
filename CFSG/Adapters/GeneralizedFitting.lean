module

public import CFSG.Open.GeneralizedFittingSelfCentralizingMilestoneDefs
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.Adapters.GeneralizedFittingTop

public section

namespace CFSG.Adapters

section Shared

variable (G : Type*) [Group G]

theorem genFittingFitting_eq_componentClassification :
    CFSG.Open.genFittingFitting G = CFSG.ComponentClassification.Fitting.subgroup G :=
  rfl

theorem genFittingLayer_eq_componentClassification :
    CFSG.Open.genFittingLayer G = CFSG.ComponentClassification.Layer.subgroup G :=
  rfl

theorem genFittingFStar_eq_componentClassification :
    CFSG.Open.genFittingFStar G = CFSG.ComponentClassification.GeneralizedFitting.subgroup G :=
  rfl

theorem genFittingFitting_eq_foundations :
    CFSG.Open.genFittingFitting G = CFSG.fittingSubgroup G :=
  rfl

theorem genFittingLayer_eq_foundations : CFSG.Open.genFittingLayer G = CFSG.layer G :=
  (CFSG.layer_eq_componentClassification G).symm

theorem genFittingFStar_eq_foundations :
    CFSG.Open.genFittingFStar G = CFSG.generalizedFitting G :=
  (CFSG.generalizedFitting_eq_componentClassification G).symm

end Shared

theorem generalizedFittingSubgroupOf_top_eq_foundations (G : Type*) [Group G] [Finite G] :
    CFSG.GorensteinWalter.generalizedFittingSubgroupOf (⊤ : Subgroup G) =
      CFSG.generalizedFitting G :=
  (generalizedFittingSubgroupOf_top_eq_componentClassification G).trans
    (CFSG.generalizedFitting_eq_componentClassification G).symm

theorem genFittingFStar_eq (G : Type*) [Group G] [Finite G] :
    CFSG.Open.genFittingFStar G =
      CFSG.GorensteinWalter.generalizedFittingSubgroupOf (⊤ : Subgroup G) :=
  (generalizedFittingSubgroupOf_top_eq_componentClassification G).symm

theorem centralizer_generalizedFittingSubgroupOf_top_le {G : Type*} [Group G] [Finite G] :
    Subgroup.centralizer
        (CFSG.GorensteinWalter.generalizedFittingSubgroupOf (⊤ : Subgroup G) : Set G) ≤
      CFSG.GorensteinWalter.generalizedFittingSubgroupOf (⊤ : Subgroup G) := by
  rw [generalizedFittingSubgroupOf_top_eq_componentClassification]
  exact CFSG.ComponentClassification.GeneralizedFitting.centralizer_le G

open CFSG.Open in
theorem generalized_fitting_self_centralizing
    (G : Type) [Group G] [Finite G] :
    Subgroup.centralizer (genFittingFStar G : Set G) ≤ genFittingFStar G :=
  CFSG.ComponentClassification.GeneralizedFitting.centralizer_le G

end CFSG.Adapters
