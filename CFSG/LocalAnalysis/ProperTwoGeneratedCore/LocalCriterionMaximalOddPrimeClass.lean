module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalOddPrimeClassCoverage
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalOddPrimeClassAffine
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffine
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalOddPrimeClassHull

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffine
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalOddPrimeClass

variable {G : Type*} [Group G] [Finite G]

theorem local_involution_point_maximal_odd_prime_normalizer_meets_distinguished_class
    (H : Subgroup G) (z : G) (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (hdoubly : ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d)
    (hcover : ∀ V : Subgroup G,
      Nonempty (V ≃* Multiplicative (ZMod 2 × ZMod 2)) →
        ∃ s ∈ V, s ∈ involutionPointClass z)
    (hhull : ∀ u : G, orderOf u = 2 → u ∉ involutionPointClass z →
      ∃ L : Subgroup G,
        L ≤ Subgroup.centralizer ({u} : Set G) ∧
        (L.subgroupOf (Subgroup.centralizer ({u} : Set G))).Normal ∧
        (∃ s ∈ L, s ∈ involutionPointClass z) ∧
        (∀ l ∈ L, orderOf l = 2 → l ∈ involutionPointClass z) ∧
        (∀ a b : pointRightCosetSpace H,
          pointRightCosetMul H a u = a → pointRightCosetMul H b u = b →
            ∃ l ∈ L, pointRightCosetMul H a l = b) ∧
        Group.IsSolvable (outerAutomorphismGroup L))
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p) (W : Subgroup G)
    (hW : IsPGroup p W) (hthree : 3 ≤ Nat.card (pointFixedSet H W))
    (hmax : ∀ V : Subgroup G, IsPGroup p V → W ≤ V →
      3 ≤ Nat.card (pointFixedSet H V) → V ≤ W) :
    ((Subgroup.normalizer (W : Set G) : Set G) ∩ involutionPointClass z).Nonempty := by
  by_contra hmeet
  have hempty : (Subgroup.normalizer (W : Set G) : Set G) ∩
      involutionPointClass z = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro g hg
    exact hmeet ⟨g, hg⟩
  have hclassfree : involutionPointClass z ∩
      (Subgroup.normalizer (W : Set G) : Set G) = ∅ := by
    rw [Set.inter_comm]
    exact hempty
  have hno := no_four_group_of_covered_class_free z
    (Subgroup.normalizer (W : Set G)) (original_four_group_coverage_klein z hcover) hclassfree
  have hKhull := global_hulls_apply_to_pointwise_kernel h (pointFixedSet H W) hthree hhull
  obtain ⟨_, _, _, _, _, _, _, ell, Q, hell, hQne, hQnormal,
      hQelementary, hQregular, _, _⟩ :=
    class_free_maximal_prime_normalizer_affine h S hzS hzcenter hdoubly
      p hp hpodd W hW hthree hmax hclassfree (original_four_group_coverage_native z hcover) hKhull
  have hpair := original_normalizer_odd_pair_count_of_regular_common_image
    H p hp W hW hthree hmax hno ell hell Q hQne hQnormal hQelementary hQregular
  exact hmeet (original_normalizer_meets_class_of_odd_pair_count
    h S hzS hzcenter p hp hpodd W hW hthree hmax hpair)

end CFSG.ProperTwoGeneratedCore
