module

public import CFSG.GroupTheory.ABGLocalTools.SL2FieldAutSemilinear
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSetup
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicDefs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityIsotropic

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoClassical (Sec3)
open CFSG.Blueprint.Chevalley CFSG.ComponentClassification.UnbalancedCatalog

section Conj

variable {G : Type} [Group G]

theorem rightConjugate_eq_self_of_mem_centralizer {T : Subgroup G} {x : G}
    (hx : x ∈ centralizer (T : Set G)) : rightConjugate T x = T := by
  ext y
  rw [mem_rightConjugate_iff]
  constructor
  · intro hy
    have h1 : x * y * x⁻¹ * x = x * (x * y * x⁻¹) := mem_centralizer_iff.1 hx _ hy
    have h2 : y = x * y * x⁻¹ := by
      calc y = x⁻¹ * (x * y * x⁻¹ * x) := by group
        _ = x⁻¹ * (x * (x * y * x⁻¹)) := by rw [h1]
        _ = x * y * x⁻¹ := by group
    rw [h2]
    exact hy
  · intro hy
    have h1 : y * x = x * y := mem_centralizer_iff.1 hx y hy
    rw [← h1, mul_inv_cancel_right]
    exact hy

end Conj

end CFSG.ComponentClassification.RankTwoExceptional
