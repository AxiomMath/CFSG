module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeneratedPairGrowthPrimePart
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionTripleSylowGeometry
public import CFSG.Assembly.OrderReductions.PrimePart

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

open CFSG.ShultStronglyClosedTI

variable {G : Type*} [Group G]

theorem generatedPairGrowth_distinguished_normalizes_triple_odd_core
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (beta : rightCosetSpace H) :
    z ∈ Subgroup.normalizer ((CFSG.oddCore (triplePointStabilizer H z beta)).map
      (triplePointStabilizer H z beta).subtype : Set G) := by
  exact (generatedPairGrowth_normalizer_le_characteristic_image
    (triplePointStabilizer H z beta) (CFSG.oddCore (triplePointStabilizer H z beta))
    (CFSG.ComponentClassification.OddCore.characteristic _))
    (LocalCriterionTripleSylow.triple_stabilizer_normalized_by_distinguished h beta)

theorem generatedPairGrowth_triple_odd_core_prime_part_eq [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    {p : ℕ} (hp : p.Prime) (P : Sylow p (pairPointStabilizer H beta))
    (hPE : (P : Subgroup (pairPointStabilizer H beta)).map
      (pairPointStabilizer H beta).subtype ≤ triplePointStabilizer H z beta) :
    CFSG.OrderReductions.PrimePart.primePart p
        (Nat.card ((CFSG.oddCore (triplePointStabilizer H z beta)).map
          (triplePointStabilizer H z beta).subtype)) =
      CFSG.OrderReductions.PrimePart.primePart p (Nat.card (pairOddCore H beta)) := by
  unfold CFSG.OrderReductions.PrimePart.primePart
  rw [generatedPairGrowth_triple_odd_core_full_prime_part h S hzS hzcenter hbeta ht hp P hPE]

theorem generatedPairGrowth_original_normalizer_growth_hypotheses
    [Finite G] [IsSimpleGroup G] (hnonabelian : ∃ a b : G, a * b ≠ b * a)
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hgen : (Subgroup.zpowers z ⊔ Subgroup.zpowers t) ⊔ pairOddCore H beta = ⊤)
    {p : ℕ} (hp : p.Prime) (P : Sylow p (pairPointStabilizer H beta))
    (hPE : (P : Subgroup (pairPointStabilizer H beta)).map
      (pairPointStabilizer H beta).subtype ≤ triplePointStabilizer H z beta) :
    let J := pairOddCore H beta
    let V := (CFSG.oddCore (triplePointStabilizer H z beta)).map
      (triplePointStabilizer H z beta).subtype
    J ≠ ⊥ ∧ Odd (Nat.card J) ∧
      (∀ N : Subgroup G, N.Normal → N ≤ J → N = ⊥) ∧
      orderOf z = 2 ∧ Subgroup.normalizer (J : Set G) ⊔ Subgroup.zpowers z = ⊤ ∧
      V ≤ J ∧ z ∈ Subgroup.normalizer (V : Set G) ∧
      CFSG.OrderReductions.PrimePart.primePart p (Nat.card V) =
        CFSG.OrderReductions.PrimePart.primePart p (Nat.card J) := by
  dsimp only
  refine ⟨generatedPairGrowth_pair_odd_core_ne_bot hnonabelian h ht hgen,
    pairOddCore_odd H beta, ?_, h.distinguished_order,
    generatedPairGrowth_normalizer_generation h hbeta ht hgen,
    triple_odd_core_le_pair_odd_core h S hzS hzcenter hbeta ht,
    generatedPairGrowth_distinguished_normalizes_triple_odd_core h beta,
    generatedPairGrowth_triple_odd_core_prime_part_eq h S hzS hzcenter hbeta ht hp P hPE⟩
  intro N hN hNJ
  let : N.Normal := hN
  exact generatedPairGrowth_normal_subgroup_in_pair_odd_core_eq_bot h beta N hNJ

end CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
