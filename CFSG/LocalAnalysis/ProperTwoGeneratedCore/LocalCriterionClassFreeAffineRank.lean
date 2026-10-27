module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineExclusion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.PermutationQuotient

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffine

open CFSG.ShultStronglyClosedTI
open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem class_free_subgroup_not_twoRankAtLeastTwo
    (z : G) (N : Subgroup G)
    (hcoverage : ∀ A : Subgroup G, IsElemAbelian 2 A → Nat.card A = 4 →
      ∃ s ∈ A, s ∈ involutionPointClass z)
    (hclassfree : involutionPointClass z ∩ (N : Set G) = ∅) :
    ¬ TwoRankAtLeastTwo N := by
  rintro ⟨E, hEcard, hEsq⟩
  let A := E.map N.subtype
  have hAcard : Nat.card A = 4 := by
    rw [Subgroup.card_map_of_injective N.subtype_injective]
    exact hEcard
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAcomm : IsMulCommutative A :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2)
      (by simpa only [show 2 ^ 2 = 4 by decide] using hAcard)
  have hAelem : IsElemAbelian 2 A := by
    refine ⟨hAcomm, ?_⟩
    intro a ha
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp ha
    exact congrArg (fun x : E => (x : G)) (hEsq ⟨e, he⟩)
  obtain ⟨s, hsA, hsclass⟩ := hcoverage A hAelem hAcard
  have hsN : s ∈ N := (Subgroup.map_subtype_le E) hsA
  have hempty : s ∈ (∅ : Set G) := hclassfree ▸ ⟨hsclass, hsN⟩
  exact hempty

theorem homomorphism_image_not_twoRankAtLeastTwo_of_odd_kernel
    {T : Type*} [Group T] (f : G →* T)
    (hkerodd : Odd (Nat.card f.ker))
    (hrank : ¬ TwoRankAtLeastTwo G) :
    ¬ TwoRankAtLeastTwo f.range := by
  have hquot := not_twoRankAtLeastTwo_quotient_of_odd f.ker hkerodd hrank
  let e := QuotientGroup.quotientKerEquivRange f
  intro himage
  exact hquot (himage.map_of_injective e.symm.toMonoidHom e.symm.injective)

theorem maximal_prime_pointwise_normalizer_not_twoRankAtLeastTwo
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
      ∃ s ∈ A, s ∈ involutionPointClass z) :
    ¬ TwoRankAtLeastTwo
      (Subgroup.normalizer (pointwiseRightStabilizer H (pointFixedSet H W) : Set G)) :=
  class_free_subgroup_not_twoRankAtLeastTwo z _ hcoverage
    (maximal_prime_pointwise_kernel_normalizer_class_free
      h S hzS hzcenter p hp W hW hthree hmax hclassfree)

theorem maximal_prime_common_image_not_twoRankAtLeastTwo_of_odd_kernel
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
    ¬ TwoRankAtLeastTwo (pointwiseKernelNormalizerImage H W) := by
  let K := pointwiseRightStabilizer H (pointFixedSet H W)
  let N := Subgroup.normalizer (K : Set G)
  have hkerodd : Odd (Nat.card (pointwiseKernelNormalizerRepresentation H W).ker) := by
    rw [pointwiseKernelNormalizerRepresentation_ker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show K ≤ N from K.le_normalizer)).toEquiv]
    exact hKodd
  exact homomorphism_image_not_twoRankAtLeastTwo_of_odd_kernel
    (pointwiseKernelNormalizerRepresentation H W) hkerodd
    (maximal_prime_pointwise_normalizer_not_twoRankAtLeastTwo
      h S hzS hzcenter p hp W hW hthree hmax hclassfree hcoverage)

end CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffine
