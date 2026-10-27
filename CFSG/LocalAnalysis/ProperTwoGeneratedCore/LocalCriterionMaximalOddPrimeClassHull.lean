module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineExclusion
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHullAutomorphisms

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalOddPrimeClass

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffine
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull

variable {G : Type*} [Group G]

theorem no_four_group_of_covered_class_free
    (z : G) (Y : Subgroup G)
    (hcover : ∀ V : Subgroup G, IsKleinFour V →
      ∃ s ∈ V, s ∈ involutionPointClass z)
    (hfree : involutionPointClass z ∩ (Y : Set G) = ∅) :
    ∀ A : Subgroup Y, ¬ IsKleinFour A := by
  intro A hA
  let := hA
  let V := A.map Y.subtype
  let e : A ≃* V := Subgroup.equivMapOfInjective A Y.subtype Y.subtype_injective
  have hV : IsKleinFour V := by
    refine ⟨?_, ?_⟩
    · exact (Nat.card_congr e.toEquiv).symm.trans IsKleinFour.card_four
    · exact (Monoid.exponent_eq_of_mulEquiv e).symm.trans IsKleinFour.exponent_two
  obtain ⟨s, hs, hsclass⟩ := hcover V hV
  have hsY : s ∈ Y := (Subgroup.map_subtype_le A) hs
  have hempty : s ∈ (∅ : Set G) := hfree ▸ ⟨hsclass, hsY⟩
  exact hempty

theorem pointwise_kernel_element_not_distinguished [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (Delta : Set (pointRightCosetSpace H)) (hthree : 3 ≤ Nat.card Delta)
    (u : G) (hu : u ∈ pointwiseRightStabilizer H Delta) :
    u ∉ involutionPointClass z := by
  intro huclass
  obtain ⟨a, ha, hmove⟩ := class_involution_moves_point_of_three_set h Delta hthree u huclass
  exact hmove ((mem_pointwiseRightStabilizer H Delta u).mp hu a ha).symm

theorem global_hulls_apply_to_pointwise_kernel [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (Delta : Set (pointRightCosetSpace H)) (hthree : 3 ≤ Nat.card Delta)
    (hhull : ∀ u : G, orderOf u = 2 → u ∉ involutionPointClass z →
      ∃ L : Subgroup G,
        L ≤ Subgroup.centralizer ({u} : Set G) ∧
        (L.subgroupOf (Subgroup.centralizer ({u} : Set G))).Normal ∧
        (∃ s ∈ L, s ∈ involutionPointClass z) ∧
        (∀ l ∈ L, orderOf l = 2 → l ∈ involutionPointClass z) ∧
        (∀ a b : pointRightCosetSpace H,
          pointRightCosetMul H a u = a → pointRightCosetMul H b u = b →
            ∃ l ∈ L, pointRightCosetMul H a l = b) ∧
        Group.IsSolvable (outerAutomorphismGroup L)) :
    ∀ u : G, u ∈ pointwiseRightStabilizer H Delta → orderOf u = 2 →
      ∃ L : Subgroup G,
        L ≤ Subgroup.centralizer ({u} : Set G) ∧
        (L.subgroupOf (Subgroup.centralizer ({u} : Set G))).Normal ∧
        (∃ s ∈ L, s ∈ involutionPointClass z) ∧
        (∀ l ∈ L, orderOf l = 2 → l ∈ involutionPointClass z) ∧
        (∀ a b : pointRightCosetSpace H,
          pointRightCosetMul H a u = a → pointRightCosetMul H b u = b →
            ∃ l ∈ L, pointRightCosetMul H a l = b) ∧
        Group.IsSolvable (outerAutomorphismGroup L) := by
  intro u hu huorder
  exact hhull u huorder (pointwise_kernel_element_not_distinguished h Delta hthree u hu)

end CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalOddPrimeClass
