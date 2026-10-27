module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointClassFreeFixedPoints

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

variable {G : Type*} [Group G] [Finite G]

theorem noncentral_pair_prime_overgroup_normalizing_class_has_no_fixed_point
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (htriple : distinguishedTripleCentralization H z)
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (t : G) (ht : t ∈ rightPairFlipFiber H z beta)
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (M : Subgroup G) (hM : IsPGroup p M)
    (hMD : M ≤ pairPointStabilizer H beta)
    (htM : t ∈ Subgroup.normalizer (M : Set G))
    (hnoncentral : ⁅M, Subgroup.zpowers t⁆ ≠ ⊥)
    (W : Subgroup G) (hMW : M ≤ W)
    (hthree : 3 ≤ Nat.card (pointFixedSet H W))
    (s : G) (hs : s ∈ involutionPointClass z)
    (hsW : s ∈ Subgroup.normalizer (W : Set G)) :
    ∀ epsilon ∈ pointFixedSet H W, pointRightCosetMul H epsilon s ≠ epsilon := by
  intro epsilon hepsilon hfixed
  have hWC := normalized_three_point_subgroup_centralizes_class_fixed_point
    htriple W hthree s hs hsW epsilon hepsilon hfixed
  have hMC := hMW.trans hWC
  have hsC : s ∈ Subgroup.centralizer (M : Set G) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (hMC hx)
  have hsM := Subgroup.centralizer_le_normalizer (M : Set G) hsC
  have hno := (noncentral_pair_odd_normalizer_entire_class_fixed_points
    h htriple beta hbeta t ht p hp hpodd M hM hMD htM hnoncentral).2
  exact hno s ⟨hs, hsM⟩ epsilon (pointFixedSet_antitone hMW hepsilon) hfixed

end CFSG.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree
