module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionAffineRankOne
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineProduct
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHullAutomorphisms
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionAffineOddPairRegular
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineDegree
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineRank

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffine

open scoped Pointwise
open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionAffineOddPair
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionAffineRankOne

variable {G : Type*} [Group G] [Finite G]

theorem class_free_maximal_prime_normalizer_affine_of_odd_kernel
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (hdoubly : ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d)
    (p : ℕ) (hp : p.Prime) (_hpodd : Odd p) (W : Subgroup G)
    (hW : IsPGroup p W) (hthree : 3 ≤ Nat.card (pointFixedSet H W))
    (hmax : ∀ V : Subgroup G, IsPGroup p V → W ≤ V →
      3 ≤ Nat.card (pointFixedSet H V) → V ≤ W)
    (hclassfree : involutionPointClass z ∩
      (Subgroup.normalizer (W : Set G) : Set G) = ∅)
    (hcoverage : ∀ A : Subgroup G, CFSG.Open.IsElemAbelian 2 A → Nat.card A = 4 →
      ∃ s ∈ A, s ∈ involutionPointClass z)
    (_hhull : ∀ u : G, u ∈ pointwiseRightStabilizer H (pointFixedSet H W) →
      orderOf u = 2 → ∃ L : Subgroup G,
        L ≤ Subgroup.centralizer ({u} : Set G) ∧
        (L.subgroupOf (Subgroup.centralizer ({u} : Set G))).Normal ∧
        (∃ r ∈ L, r ∈ involutionPointClass z) ∧
        (∀ l ∈ L, orderOf l = 2 → l ∈ involutionPointClass z) ∧
        (∀ a b : pointRightCosetSpace H,
          pointRightCosetMul H a u = a → pointRightCosetMul H b u = b →
          ∃ l ∈ L, pointRightCosetMul H a l = b) ∧
        Group.IsSolvable (outerAutomorphismGroup L))
    (hKodd : Odd (Nat.card (pointwiseRightStabilizer H (pointFixedSet H W)))) :
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
  let : MulAction.IsMultiplyPretransitive
      (pointwiseKernelNormalizerImage H W) (pointFixedSet H W) 2 := htwo
  let : MulAction.IsPretransitive
      (pointwiseKernelNormalizerImage H W) (pointFixedSet H W) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  let : Nontrivial (pointFixedSet H W) :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let F := pointwiseKernelNormalizerImage H W
  obtain ⟨a⟩ := (inferInstance : Nonempty (pointFixedSet H W))
  have heven := maximal_prime_common_induced_image_even
    H hdoubly p hp W hW hthree hmax
  have hrank := maximal_prime_common_image_not_twoRankAtLeastTwo_of_odd_kernel
    h S hzS hzcenter p hp W hW hthree hmax hclassfree hcoverage hKodd
  have hstabilizer := maximal_prime_common_induced_image_stabilizer_isCoatom
    H hdoubly p hp W hW hthree hmax a
  obtain ⟨_, ell, Q, hQnormal, hell, _, hQne, _, hQelementary,
      _, _, _, _, hQregular, _, _, _, hcard, _, _, hprimepower⟩ :=
    rank_one_primitive_odd_affine_core heven hrank hthree a hstabilizer
  have hregular : RegularOnEntire F Q := hQregular
  exact ⟨maximal_prime_pointwise_kernel_normalizer_class_free
      h S hzS hzcenter p hp W hW hthree hmax hclassfree,
    globally_maximal_prime_is_sylow_pointwise_kernel H p W hW hthree hmax,
    maximal_prime_pointwise_kernel_normalizer_set_product H p hp W hW hthree hmax,
    pointwiseKernelNormalizerRepresentation_ker H W,
    maximal_prime_normalizer_representation_ranges_eq H p hp W hW hthree hmax,
    pointwiseKernelNormalizerImage_faithful H W, htwo,
    ell, Q, hell, hQne, hQnormal, hQelementary, hregular, hcard, hprimepower⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffine
