module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineRank
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHullConjugacy

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffine

open CFSG.Open CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull

variable {G : Type*} [Group G] [Finite G]

theorem twoRank_le_one_of_not_twoRankAtLeastTwo
    (hrank : ¬ TwoRankAtLeastTwo G) : twoRank G ≤ 1 := by
  apply twoRank_le_one_of_no_four_group
  intro V hV hcard
  apply hrank
  refine ⟨V, hcard, ?_⟩
  intro v
  exact Subtype.ext (hV.2 v v.property)

theorem maximal_prime_common_image_twoRank_le_one_of_odd_kernel
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (p : ℕ) (hp : p.Prime) (W : Subgroup G)
    (hW : IsPGroup p W) (hthree : 3 ≤ Nat.card (pointFixedSet H W))
    (hmax : ∀ V : Subgroup G, IsPGroup p V → W ≤ V →
      3 ≤ Nat.card (pointFixedSet H V) → V ≤ W)
    (hclassfree : involutionPointClass z ∩
      (Subgroup.normalizer (W : Set G) : Set G) = ∅)
    (hcoverage : ∀ A : Subgroup G, IsElemAbelian 2 A → Nat.card A = 4 →
      ∃ s ∈ A, s ∈ involutionPointClass z)
    (hKodd : Odd (Nat.card (pointwiseRightStabilizer H (pointFixedSet H W)))) :
    twoRank (pointwiseKernelNormalizerImage H W) ≤ 1 :=
  twoRank_le_one_of_not_twoRankAtLeastTwo
    (maximal_prime_common_image_not_twoRankAtLeastTwo_of_odd_kernel
      h S hzS hzcenter p hp W hW hthree hmax hclassfree hcoverage hKodd)

end CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffine
