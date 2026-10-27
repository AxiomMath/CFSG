module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizerCosets
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizerTransport

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizer

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow

variable {G : Type*} [Group G]

theorem restrictedRightCosetEmbedding_eq_native (H N : Subgroup G) :
    restrictedRightCosetEmbedding H N = subgroupRightCosetInclusion H N := rfl

theorem normalizerRightCosetFixedEmbedding_surjective
    (H A : Subgroup G) (hAH : A ≤ H)
    (htrans : ∀ a b : pointRightCosetSpace H, a ∈ pointFixedSet H A →
      b ∈ pointFixedSet H A →
      ∃ n : G, n ∈ Subgroup.normalizer (A : Set G) ∧ pointRightCosetMul H a n = b) :
    Function.Surjective (normalizerRightCosetFixedEmbedding H A hAH) := by
  intro a
  have hbase : rightCosetMk H 1 ∈ pointFixedSet H A := by
    intro g hg
    exact (point_right_base_fixed_iff H g).mpr (hAH hg)
  obtain ⟨n, hn, hna⟩ := htrans (rightCosetMk H 1) a.val hbase a.property
  refine ⟨rightCosetMk (H.subgroupOf (Subgroup.normalizer (A : Set G))) ⟨n, hn⟩, ?_⟩
  apply Subtype.ext
  change rightCosetMk H n = a.val
  simpa only [rightCosetMk, pointRightCosetMul_mk, one_mul] using hna

@[expose] def normalizerRightCosetFixedEquiv
    (H A : Subgroup G) (hAH : A ≤ H)
    (htrans : ∀ a b : pointRightCosetSpace H, a ∈ pointFixedSet H A →
      b ∈ pointFixedSet H A →
      ∃ n : G, n ∈ Subgroup.normalizer (A : Set G) ∧ pointRightCosetMul H a n = b) :
    pointRightCosetSpace (H.subgroupOf (Subgroup.normalizer (A : Set G))) ≃
      pointFixedSet H A :=
  Equiv.ofBijective (normalizerRightCosetFixedEmbedding H A hAH)
    ⟨normalizerRightCosetFixedEmbedding_injective H A hAH,
      normalizerRightCosetFixedEmbedding_surjective H A hAH htrans⟩

theorem normalizerRightCosetFixedEquiv_mk
    (H A : Subgroup G) (hAH : A ≤ H)
    (htrans : ∀ a b : pointRightCosetSpace H, a ∈ pointFixedSet H A →
      b ∈ pointFixedSet H A →
      ∃ n : G, n ∈ Subgroup.normalizer (A : Set G) ∧ pointRightCosetMul H a n = b)
    (n : Subgroup.normalizer (A : Set G)) :
    (normalizerRightCosetFixedEquiv H A hAH htrans
      (rightCosetMk (H.subgroupOf (Subgroup.normalizer (A : Set G))) n)).val =
        rightCosetMk H (n : G) := rfl

theorem normalizerRightCosetFixedEquiv_equivariant
    (H A : Subgroup G) (hAH : A ≤ H)
    (htrans : ∀ a b : pointRightCosetSpace H, a ∈ pointFixedSet H A →
      b ∈ pointFixedSet H A →
      ∃ n : G, n ∈ Subgroup.normalizer (A : Set G) ∧ pointRightCosetMul H a n = b)
    (a : pointRightCosetSpace (H.subgroupOf (Subgroup.normalizer (A : Set G))))
    (n : Subgroup.normalizer (A : Set G)) :
    (normalizerRightCosetFixedEquiv H A hAH htrans
      (pointRightCosetMul (H.subgroupOf (Subgroup.normalizer (A : Set G))) a n)).val =
        pointRightCosetMul H (normalizerRightCosetFixedEquiv H A hAH htrans a).val (n : G) :=
  restrictedRightCosetEmbedding_equivariant H (Subgroup.normalizer (A : Set G)) a n

theorem original_triple_sylow_normalizer_transitive [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (hdoubly : ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (p : ℕ) (hp : p.Prime) (P : Sylow p (triplePointStabilizer H z beta))
    (hzP : z ∈ Subgroup.normalizer
      (((P : Subgroup (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype : Subgroup G) : Set G)) :
    ∀ a b : pointRightCosetSpace H,
      a ∈ pointFixedSet H ((P : Subgroup (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype) →
      b ∈ pointFixedSet H ((P : Subgroup (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype) →
      ∃ n : G,
        n ∈ Subgroup.normalizer
          (((P : Subgroup (triplePointStabilizer H z beta)).map
            (triplePointStabilizer H z beta).subtype : Subgroup G) : Set G) ∧
        pointRightCosetMul H a n = b := by
  have hh := original_triple_sylow_normalizer_action h S hzS hzcenter hdoubly beta hbeta p hp P hzP
  intro a b ha hb
  by_cases hab : a = b
  · exact ⟨1, (Subgroup.normalizer _).one_mem, (pointRightCosetMul_one H a).trans hab⟩
  · obtain ⟨n, hn, hna, _⟩ := hh.2.2.2.2.2.2 a b b a ha hb hb ha hab (Ne.symm hab)
    exact ⟨n, hn, hna⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizer
