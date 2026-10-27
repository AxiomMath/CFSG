module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalOddPrimeClassPair
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionAffineOddPair
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimePairTransport

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalOddPrimeClass

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffine
open CFSG.ProperTwoGeneratedCore.LocalCriterionAffineOddPair

variable {G : Type*} [Group G] [Finite G]

theorem original_normalizer_odd_pair_count_of_regular_common_image
    (H : Subgroup G) (p : ℕ) (hp : p.Prime) (W : Subgroup G)
    (hW : IsPGroup p W) (hthree : 3 ≤ Nat.card (pointFixedSet H W))
    (hmax : ∀ V : Subgroup G, IsPGroup p V → W ≤ V →
      3 ≤ Nat.card (pointFixedSet H V) → V ≤ W)
    (hno : ∀ A : Subgroup (Subgroup.normalizer (W : Set G)), ¬ IsKleinFour A)
    (ell : ℕ) (hell : ell.Prime) (Q : Subgroup (pointwiseKernelNormalizerImage H W))
    (hQne : Q ≠ ⊥) (hQnormal : Q.Normal)
    (hQelementary : IsElementaryAbelian ell Q)
    (hQregular : RegularOnEntire (pointwiseKernelNormalizerImage H W) Q) :
    let Y := Subgroup.normalizer (W : Set G)
    letI := pointInvariantSetInverseRightAction H Y (pointFixedSet H W)
      (fun _ hn _ homega => normalizer_preserves_pointFixedSet hn homega)
    ∀ A : Subgroup Y, Odd (Nat.card A) →
      ∀ alpha beta : pointFixedSet H W, alpha ≠ beta →
        (∀ g ∈ A, g • alpha = alpha) → (∀ g ∈ A, g • beta = beta) →
          3 ≤ Nat.card (MulAction.fixedPoints A (pointFixedSet H W)) := by
  let Y := Subgroup.normalizer (W : Set G)
  let := pointInvariantSetInverseRightAction H Y (pointFixedSet H W)
    (fun _ hn _ homega => normalizer_preserves_pointFixedSet hn homega)
  have hdata : ∃ R : Subgroup ((MulAction.toPermHom Y (pointFixedSet H W)).range),
      R ≠ ⊥ ∧ R.Normal ∧ IsElementaryAbelian ell R ∧
        RegularOnEntire (MulAction.toPermHom Y (pointFixedSet H W)).range R := by
    change ∃ R : Subgroup (primeNormalizerRepresentation H W).range,
      R ≠ ⊥ ∧ R.Normal ∧ IsElementaryAbelian ell R ∧
        RegularOnEntire (primeNormalizerRepresentation H W).range R
    rw [maximal_prime_normalizer_representation_ranges_eq H p hp W hW hthree hmax]
    exact ⟨Q, hQne, hQnormal, hQelementary, hQregular⟩
  obtain ⟨R, hRne, hRnormal, hRelementary, hRregular⟩ := hdata
  let := hRnormal
  let : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot R).mpr hRne
  exact (rank_one_cover_affine_odd_pair_subgroups_fix_three_points
    (no_four_group_iff_no_binary_product_subgroup.mp hno) hthree R
    ⟨ell, hell, hRelementary⟩ hRregular).1

theorem original_normalizer_meets_class_of_odd_pair_count
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p) (W : Subgroup G)
    (hW : IsPGroup p W) (hthree : 3 ≤ Nat.card (pointFixedSet H W))
    (hmax : ∀ V : Subgroup G, IsPGroup p V → W ≤ V →
      3 ≤ Nat.card (pointFixedSet H V) → V ≤ W)
    (hpair :
      let Y := Subgroup.normalizer (W : Set G)
      letI := pointInvariantSetInverseRightAction H Y (pointFixedSet H W)
        (fun _ hn _ homega => normalizer_preserves_pointFixedSet hn homega)
      ∀ A : Subgroup Y, Odd (Nat.card A) →
        ∀ alpha beta : pointFixedSet H W, alpha ≠ beta →
          (∀ g ∈ A, g • alpha = alpha) → (∀ g ∈ A, g • beta = beta) →
            3 ≤ Nat.card (MulAction.fixedPoints A (pointFixedSet H W))) :
    ((Subgroup.normalizer (W : Set G) : Set G) ∩ involutionPointClass z).Nonempty := by
  let : Nontrivial (pointFixedSet H W) :=
    Finite.one_lt_card_iff_nontrivial.mp (show 1 < Nat.card (pointFixedSet H W) by omega)
  obtain ⟨a, b, hab⟩ := exists_pair_ne (pointFixedSet H W)
  obtain ⟨Q, hQ⟩ := maximal_prime_sylow_pair_of_odd_pair_count H p hp hpodd W hW hmax a b hab hpair
  have habval : a.val ≠ b.val := fun heq => hab (Subtype.ext heq)
  obtain ⟨r, hrclass, _, _, hrnormal, _⟩ :=
    pair_specified_sylow_flip h S hzS hzcenter a.val b.val habval p hp Q
  rw [hQ] at hrnormal
  exact ⟨r, hrnormal, hrclass⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalOddPrimeClass
