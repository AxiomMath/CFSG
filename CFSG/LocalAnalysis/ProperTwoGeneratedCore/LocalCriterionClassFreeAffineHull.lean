module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHullKernel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineRank

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffine
open CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G] [Finite G]

theorem maximal_prime_common_image_isSolvable_of_involution
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (_hdoubly : ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d)
    (p : ℕ) (hp : p.Prime) (_hodd : Odd p) (W : Subgroup G)
    (hW : IsPGroup p W) (hthree : 3 ≤ Nat.card (pointFixedSet H W))
    (hmax : ∀ V : Subgroup G, IsPGroup p V → W ≤ V →
      3 ≤ Nat.card (pointFixedSet H V) → V ≤ W)
    (hclassfree : involutionPointClass z ∩
      (Subgroup.normalizer (W : Set G) : Set G) = ∅)
    (hcoverage : ∀ A : Subgroup G, CFSG.Open.IsElemAbelian 2 A → Nat.card A = 4 →
      ∃ s ∈ A, s ∈ involutionPointClass z)
    (u : G) (huK : u ∈ pointwiseRightStabilizer H (pointFixedSet H W))
    (hu : orderOf u = 2)
    (hhull : ∀ v : G, v ∈ pointwiseRightStabilizer H (pointFixedSet H W) →
      orderOf v = 2 → ∃ L : Subgroup G,
        L ≤ Subgroup.centralizer ({v} : Set G) ∧
        (L.subgroupOf (Subgroup.centralizer ({v} : Set G))).Normal ∧
        (∃ r ∈ L, r ∈ involutionPointClass z) ∧
        (∀ l ∈ L, orderOf l = 2 → l ∈ involutionPointClass z) ∧
        (∀ a b : pointRightCosetSpace H,
          pointRightCosetMul H a v = a → pointRightCosetMul H b v = b →
          ∃ l ∈ L, pointRightCosetMul H a l = b) ∧
        Group.IsSolvable (outerAutomorphismGroup L)) :
    Group.IsSolvable (pointwiseKernelNormalizerImage H W) := by
  let K := pointwiseRightStabilizer H (pointFixedSet H W)
  have hNclassfree : involutionPointClass z ∩
      (Subgroup.normalizer (K : Set G) : Set G) = ∅ :=
    maximal_prime_pointwise_kernel_normalizer_class_free
      h S hzS hzcenter p hp W hW hthree hmax hclassfree
  have hKclassfree : involutionPointClass z ∩ (K : Set G) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro s ⟨hsclass, hsK⟩
    have hempty : s ∈ (∅ : Set G) :=
      hNclassfree ▸ ⟨hsclass, Subgroup.le_normalizer hsK⟩
    exact hempty
  have hKrank : ¬ TwoRankAtLeastTwo K :=
    class_free_subgroup_not_twoRankAtLeastTwo z K hcoverage hKclassfree
  have hno : ∀ V : Subgroup K, CFSG.Open.IsElemAbelian 2 V → Nat.card V ≠ 4 := by
    intro V hV hcard
    apply hKrank
    refine ⟨V, hcard, ?_⟩
    intro v
    exact Subtype.ext (hV.2 v.val v.property)
  obtain ⟨L, hLC, hLnormal, hr, hLclass, htrans, hOut⟩ := hhull u huK hu
  let : Group.IsSolvable (outerAutomorphismGroup L) := hOut
  exact pointwise_kernel_normalizer_image_isSolvable_of_hull
    h W hno hNclassfree u huK hu L hLC hLnormal hr hLclass htrans

theorem maximal_prime_common_image_isSolvable_of_even_kernel
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (hdoubly : ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d)
    (p : ℕ) (hp : p.Prime) (hodd : Odd p) (W : Subgroup G)
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
    Group.IsSolvable (pointwiseKernelNormalizerImage H W) := by
  let K := pointwiseRightStabilizer H (pointFixedSet H W)
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := K) 2
    (even_iff_two_dvd.mp hKeven)
  exact maximal_prime_common_image_isSolvable_of_involution
    h S hzS hzcenter hdoubly p hp hodd W hW hthree hmax hclassfree hcoverage
    u u.property ((Subgroup.orderOf_coe u).trans hu) hhull

end CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
