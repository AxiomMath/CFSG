module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineFrattini
public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalOddFixedAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointClassFreeConclusions

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffine

open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalOddFixed
open CFSG.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree

variable {G : Type*} [Group G]

@[expose] def inverseRightRepresentation (H A : Subgroup G)
    (Delta : Set (pointRightCosetSpace H))
    (hstable : ∀ a ∈ A, ∀ omega ∈ Delta,
      pointRightCosetMul H omega a ∈ Delta) : A →* Equiv.Perm Delta :=
  letI := pointInvariantSetInverseRightAction H A Delta hstable
  MulAction.toPermHom A Delta

theorem inverseRightRepresentation_apply (H A : Subgroup G)
    (Delta : Set (pointRightCosetSpace H))
    (hstable : ∀ a ∈ A, ∀ omega ∈ Delta,
      pointRightCosetMul H omega a ∈ Delta)
    (a : A) (omega : Delta) :
    ((inverseRightRepresentation H A Delta hstable a omega : Delta) :
      pointRightCosetSpace H) = pointRightCosetMul H omega.val (a : G)⁻¹ := rfl

theorem inverseRightRepresentation_ker (H A : Subgroup G)
    (Delta : Set (pointRightCosetSpace H))
    (hstable : ∀ a ∈ A, ∀ omega ∈ Delta,
      pointRightCosetMul H omega a ∈ Delta) :
    (inverseRightRepresentation H A Delta hstable).ker =
      (pointwiseRightStabilizer H Delta).subgroupOf A := by
  ext a
  rw [MonoidHom.mem_ker, Equiv.Perm.ext_iff]
  constructor
  · intro hf
    have hinv : (a : G)⁻¹ ∈ pointwiseRightStabilizer H Delta := by
      rw [mem_pointwiseRightStabilizer]
      intro omega homega
      exact congrArg Subtype.val (hf ⟨omega, homega⟩)
    exact (pointwiseRightStabilizer H Delta).inv_mem_iff.mp hinv
  · intro ha omega
    apply Subtype.ext
    exact (mem_pointwiseRightStabilizer H Delta _).mp
      ((pointwiseRightStabilizer H Delta).inv_mem ha) omega.val omega.property

@[expose] def primeNormalizerRepresentation (H W : Subgroup G) :
    Subgroup.normalizer (W : Set G) →* Equiv.Perm (pointFixedSet H W) :=
  inverseRightRepresentation H _ _
    (fun _ hn _ homega => normalizer_preserves_pointFixedSet hn homega)

@[expose] def pointwiseKernelNormalizerRepresentation (H W : Subgroup G) :
    Subgroup.normalizer
      (pointwiseRightStabilizer H (pointFixedSet H W) : Set G) →*
        Equiv.Perm (pointFixedSet H W) :=
  inverseRightRepresentation H _ _
    (fun n hn omega homega =>
      pointwise_kernel_normalizer_preserves_fixed_set H W n hn omega homega)

@[expose] def pointwiseKernelNormalizerImage (H W : Subgroup G) :
    Subgroup (Equiv.Perm (pointFixedSet H W)) :=
  (pointwiseKernelNormalizerRepresentation H W).range

theorem pointwiseKernelNormalizerRepresentation_ker (H W : Subgroup G) :
    (pointwiseKernelNormalizerRepresentation H W).ker =
      (pointwiseRightStabilizer H (pointFixedSet H W)).subgroupOf
        (Subgroup.normalizer (pointwiseRightStabilizer H (pointFixedSet H W) : Set G)) :=
  inverseRightRepresentation_ker H _ _ _

theorem pointwiseKernelNormalizerRepresentation_ker_ambient (H W : Subgroup G) :
    (pointwiseKernelNormalizerRepresentation H W).ker.map
      (Subgroup.normalizer
        (pointwiseRightStabilizer H (pointFixedSet H W) : Set G)).subtype =
      pointwiseRightStabilizer H (pointFixedSet H W) := by
  rw [pointwiseKernelNormalizerRepresentation_ker]
  exact Subgroup.map_subgroupOf_eq_of_le (Subgroup.le_normalizer)

theorem pointwiseKernelNormalizerImage_faithful (H W : Subgroup G) :
    FaithfulSMul (pointwiseKernelNormalizerImage H W) (pointFixedSet H W) :=
  inferInstance

theorem maximal_prime_normalizer_representation_ranges_eq [Finite G]
    (H : Subgroup G) (p : ℕ) (hp : p.Prime) (W : Subgroup G)
    (hW : IsPGroup p W) (hthree : 3 ≤ Nat.card (pointFixedSet H W))
    (hmax : ∀ V : Subgroup G, IsPGroup p V → W ≤ V →
      3 ≤ Nat.card (pointFixedSet H V) → V ≤ W) :
    (primeNormalizerRepresentation H W).range = pointwiseKernelNormalizerImage H W := by
  let K := pointwiseRightStabilizer H (pointFixedSet H W)
  let N := Subgroup.normalizer (K : Set G)
  let Y := Subgroup.normalizer (W : Set G)
  have hYN : Y ≤ N := prime_normalizer_le_pointwise_kernel_normalizer H W
  have hKN : K ≤ N := K.le_normalizer
  ext f
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨⟨y, hYN y.property⟩, hy⟩
  · rintro ⟨n, hn⟩
    obtain ⟨k, hk, y, hy, hprod⟩ :=
      (maximal_prime_pointwise_kernel_frattini H p hp W hW hthree hmax).2 n n.property
    let kN : N := ⟨k, hKN hk⟩
    let yN : N := ⟨y, hYN hy⟩
    have hnprod : n = kN * yN := Subtype.ext hprod.symm
    have hkrep : pointwiseKernelNormalizerRepresentation H W kN = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [pointwiseKernelNormalizerRepresentation_ker]
      exact hk
    refine ⟨⟨y, hy⟩, ?_⟩
    rw [← hn, hnprod, map_mul, hkrep, one_mul]
    rfl

theorem maximal_prime_common_induced_image_two_pretransitive [Finite G]
    (H : Subgroup G)
    (hdoubly : ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d)
    (p : ℕ) (hp : p.Prime) (W : Subgroup G) (hW : IsPGroup p W)
    (hthree : 3 ≤ Nat.card (pointFixedSet H W))
    (hmax : ∀ V : Subgroup G, IsPGroup p V → W ≤ V →
      3 ≤ Nat.card (pointFixedSet H V) → V ≤ W) :
    MulAction.IsMultiplyPretransitive
      (pointwiseKernelNormalizerImage H W) (pointFixedSet H W) 2 := by
  let Y := Subgroup.normalizer (W : Set G)
  let := pointInvariantSetInverseRightAction H Y (pointFixedSet H W)
    (fun _ hn _ homega => normalizer_preserves_pointFixedSet hn homega)
  have htwo : MulAction.IsMultiplyPretransitive Y (pointFixedSet H W) 2 :=
    maximal_three_point_normalizer_two_pretransitive H hdoubly p hp W hW hthree hmax
  have himages := maximal_prime_normalizer_representation_ranges_eq H p hp W hW hthree hmax
  rw [MulAction.is_two_pretransitive_iff]
  intro a b c d hab hcd
  obtain ⟨y, hya, hyb⟩ := (MulAction.is_two_pretransitive_iff.mp htwo) hab hcd
  have hymem : primeNormalizerRepresentation H W y ∈ pointwiseKernelNormalizerImage H W := by
    rw [← himages]
    exact ⟨y, rfl⟩
  exact ⟨⟨primeNormalizerRepresentation H W y, hymem⟩, hya, hyb⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffine
