module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionProperHullTripleCentralization
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionProperHullBranches

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree
open scoped Pointwise

universe u

variable {G : Type u} [Group G] [Finite G]

theorem properHull_dichotomy
    {H Y : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (K : Type u) [Group K] [Finite K], Nat.card K < Nat.card G →
      2 ≤ twoRank K → (∃ A : Subgroup K, fusionStronglyEmbedded A) → R1Full K)
    (hY : Y < ⊤) (hzY : z ∈ Y) (hescape : ¬ Y ≤ H) :
    fusionStronglyEmbedded (H.subgroupOf (properHull Y z)) ∧
      conjugacyWithin Y z = conjugacyWithin (properHull Y z) z ∧
      Xor (ProperHullRankOne H Y z hzY) (ProperHullRankTwo Y z) :=
  properHull_dichotomy_of_triple h
    (properHull_minimal_failure_distinguished_triple_centralization h hcomm hsmallerR1)
    hsmallerR1 hY hzY hescape

theorem minimalLocalFailure_proper_local_hull_dichotomy
    {H Y : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (K : Type u) [Group K] [Finite K], Nat.card K < Nat.card G →
      2 ≤ twoRank K → (∃ A : Subgroup K, fusionStronglyEmbedded A) → R1Full K)
    (hY : Y < ⊤) (hzY : z ∈ Y) (hescape : ¬ Y ≤ H) :
    let L := Subgroup.closure (conjugacyWithin Y z)
    let R := (CFSG.oddCore Y).map Y.subtype
    fusionStronglyEmbedded (H.subgroupOf L) ∧
      conjugacyWithin Y z = conjugacyWithin L z ∧
      Xor
        (twoRank L = 1 ∧
          (QuotientGroup.mk (⟨z, hzY⟩ : Y) : Y ⧸ CFSG.oddCore Y) ∈
            Subgroup.center (Y ⧸ CFSG.oddCore Y) ∧
          (Y : Set G) = (Y ⊓ Subgroup.centralizer ({z} : Set G) : Set G) *
            (R : Set G) ∧
          H ⊓ Y = Y ⊓ Subgroup.centralizer ({z} : Set G) ∧
          conjugacyWithin H z ∩ (Y : Set G) = {z})
        (2 ≤ twoRank L ∧
          ⁅R, L⁆ = ⊥ ∧
          R1Full L ∧
          (∃ _ : (⊤ : Subgroup L).Normal,
            CFSG.oddCore L < ⊤ ∧ Odd (⊤ : Subgroup L).index ∧
              fusionIsBenderGroup ((⊤ : Subgroup L) ⧸
                (CFSG.oddCore L).subgroupOf ⊤)) ∧
          fusionIsBenderGroup (L ⧸ CFSG.oddCore L) ∧
          ExplicitRankOneModel (L ⧸ CFSG.oddCore L)) := by
  exact properHull_dichotomy h hcomm hsmallerR1 hY hzY hescape

end CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull
