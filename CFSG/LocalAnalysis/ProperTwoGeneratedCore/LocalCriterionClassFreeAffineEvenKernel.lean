module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineSolvable
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineProduct

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffine

open scoped Pointwise
open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionAffineOddPair
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull

variable {G : Type*} [Group G] [Finite G]

theorem class_free_maximal_prime_normalizer_affine_of_even_kernel
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (hdoubly : ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d)
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p) (W : Subgroup G)
    (hW : IsPGroup p W) (hthree : 3 ≤ Nat.card (pointFixedSet H W))
    (hmax : ∀ V : Subgroup G, IsPGroup p V → W ≤ V →
      3 ≤ Nat.card (pointFixedSet H V) → V ≤ W)
    (hclassfree : involutionPointClass z ∩
      (Subgroup.normalizer (W : Set G) : Set G) = ∅)
    (hcoverage : ∀ A : Subgroup G, CFSG.Open.IsElemAbelian 2 A → Nat.card A = 4 →
      ∃ s ∈ A, s ∈ involutionPointClass z)
    (hhull : ∀ u : G, u ∈ pointwiseRightStabilizer H (pointFixedSet H W) →
      orderOf u = 2 → ∃ L : Subgroup G,
        L ≤ Subgroup.centralizer ({u} : Set G) ∧
        (L.subgroupOf (Subgroup.centralizer ({u} : Set G))).Normal ∧
        (∃ r ∈ L, r ∈ involutionPointClass z) ∧
        (∀ l ∈ L, orderOf l = 2 → l ∈ involutionPointClass z) ∧
        (∀ a b : pointRightCosetSpace H,
          pointRightCosetMul H a u = a → pointRightCosetMul H b u = b →
          ∃ l ∈ L, pointRightCosetMul H a l = b) ∧
        Group.IsSolvable (outerAutomorphismGroup L))
    (hKeven : Even (Nat.card (pointwiseRightStabilizer H (pointFixedSet H W)))) :
    let K := pointwiseRightStabilizer H (pointFixedSet H W)
    let N := Subgroup.normalizer (K : Set G)
    let F := pointwiseKernelNormalizerImage H W
    involutionPointClass z ∩ (N : Set G) = ∅ ∧
      (∃ P : Sylow p K, (P : Subgroup K).map K.subtype = W) ∧
      (N : Set G) = (K : Set G) * (Subgroup.normalizer (W : Set G) : Set G) ∧
      (pointwiseKernelNormalizerRepresentation H W).ker = K.subgroupOf N ∧
      (primeNormalizerRepresentation H W).range = F ∧
      FaithfulSMul F (pointFixedSet H W) ∧
      MulAction.IsMultiplyPretransitive F (pointFixedSet H W) 2 ∧
      ∃ (ell : ℕ) (Q : Subgroup F), ell.Prime ∧ Q ≠ ⊥ ∧ Q.Normal ∧
        IsElementaryAbelian ell Q ∧ RegularOnEntire F Q ∧
        Nat.card (pointFixedSet H W) = Nat.card Q ∧
        IsPrimePow (Nat.card (pointFixedSet H W)) := by
  have htwo := maximal_prime_common_induced_image_two_pretransitive
    H hdoubly p hp W hW hthree hmax
  have hsolvable := maximal_prime_common_image_isSolvable_of_even_kernel
    h S hzS hzcenter hdoubly p hp hpodd W hW hthree hmax hclassfree hcoverage hhull hKeven
  exact ⟨maximal_prime_pointwise_kernel_normalizer_class_free
      h S hzS hzcenter p hp W hW hthree hmax hclassfree,
    globally_maximal_prime_is_sylow_pointwise_kernel H p W hW hthree hmax,
    maximal_prime_pointwise_kernel_normalizer_set_product H p hp W hW hthree hmax,
    pointwiseKernelNormalizerRepresentation_ker H W,
    maximal_prime_normalizer_representation_ranges_eq H p hp W hW hthree hmax,
    pointwiseKernelNormalizerImage_faithful H W, htwo,
    solvable_two_pretransitive_regular_elementary_subgroup
      (pointwiseKernelNormalizerImage H W) htwo (by omega) hsolvable⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffine
