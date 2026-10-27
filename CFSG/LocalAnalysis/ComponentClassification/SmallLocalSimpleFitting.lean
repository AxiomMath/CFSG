module

public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.ComponentClassification.SmallLocal

open Subgroup CFSG.LocalCores

theorem simple_generalized_fitting_self (G : Type*) [Group G] [IsSimpleGroup G]
    (hG : ∃ a b : G, a * b ≠ b * a) :
    Group.IsPerfect G ∧ CFSG.IsQuasisimple G ∧ IsComponent (⊤ : Subgroup G) ∧ layer G = ⊤ ∧
      generalizedFitting G = ⊤ := by
  obtain ⟨hQ, -⟩ := isQuasisimple_of_isSimpleGroup hG
  have hcomp : IsComponent (⊤ : Subgroup G) :=
    ⟨isQuasisimple_of_mulEquiv topEquiv.symm hQ, normal_top.isSubnormal⟩
  have hlayer : layer G = ⊤ := eq_top_iff.mpr (component_le_layer hcomp)
  refine ⟨hQ.1, hQ, hcomp, hlayer, ?_⟩
  change fittingSubgroup G ⊔ layer G = ⊤
  rw [hlayer, sup_top_eq]

theorem simple_generalized_fitting_self_local (G : Type*) [Group G] [IsSimpleGroup G]
    (hG : ∃ a b : G, a * b ≠ b * a) :
    Group.IsPerfect G ∧ CFSG.Open.IsQuasisimple G ∧
      CFSG.Open.IsComponentOf (⊤ : Subgroup G) ⊤ ∧ Layer.subgroup G = ⊤ ∧
      GeneralizedFitting.subgroup G = ⊤ := by
  have hP : Group.IsPerfect G := ⟨Helpers.commutator_eq_top G hG⟩
  have hQ : CFSG.Open.IsQuasisimple G := Quasisimple.simple_of_perfect G
  have hcomp : CFSG.Open.IsComponentOf (⊤ : Subgroup G) ⊤ :=
    ⟨le_rfl, .refl ⊤, Components.quasisimple_of_equiv topEquiv hQ⟩
  have hlayer : Layer.subgroup G = ⊤ := top_unique (Layer.component_le hcomp)
  refine ⟨hP, hQ, hcomp, hlayer, ?_⟩
  change Fitting.subgroup G ⊔ Layer.subgroup G = ⊤
  rw [hlayer, sup_top_eq]

end CFSG.ComponentClassification.SmallLocal
