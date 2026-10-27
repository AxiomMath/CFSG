module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeneratedPairGrowthPair
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeneratedPairGrowthSylow

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

open CFSG.ShultStronglyClosedTI

variable {G : Type*} [Group G] [Finite G]

theorem generatedPairGrowth_triple_odd_core_contains_pair_core_sylow
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    {p : ℕ} (hp : p.Prime) (P : Sylow p (pairPointStabilizer H beta))
    (hPE : (P : Subgroup (pairPointStabilizer H beta)).map
      (pairPointStabilizer H beta).subtype ≤ triplePointStabilizer H z beta) :
    ∃ R : Sylow p (pairOddCore H beta),
      (R : Subgroup (pairOddCore H beta)).map (pairOddCore H beta).subtype ≤
        (CFSG.oddCore (triplePointStabilizer H z beta)).map
          (triplePointStabilizer H z beta).subtype := by
  let B := pairPointStabilizer H beta
  let E := triplePointStabilizer H z beta
  let O := CFSG.oddCore B
  let J := pairOddCore H beta
  let : Fact p.Prime := ⟨hp⟩
  let e : O ≃* J := O.equivMapOfInjective B.subtype B.subtype_injective
  obtain ⟨R, hR⟩ := generatedPairGrowth_sylow_intersection_normal hp O P
  have hf : Function.Surjective e.toMonoidHom := e.surjective
  let R' : Sylow p J := R.mapSurjective hf
  have hcomp : J.subtype.comp e.toMonoidHom = B.subtype.comp O.subtype := by
    ext a
    rfl
  have himage : (R' : Subgroup J).map J.subtype =
      (P : Subgroup B).map B.subtype ⊓ J := by
    dsimp only [R']
    rw [Sylow.coe_mapSurjective, Subgroup.map_map, hcomp, ← Subgroup.map_map, hR,
      Subgroup.map_inf _ _ _ B.subtype_injective]
    rfl
  refine ⟨R', ?_⟩
  rw [generatedPairGrowth_triple_odd_core_eq_intersection h S hzS hzcenter hbeta ht]
  change (R' : Subgroup J).map J.subtype ≤ J ⊓ E
  rw [himage]
  exact le_inf inf_le_right (inf_le_left.trans hPE)

theorem generatedPairGrowth_triple_odd_core_full_prime_part
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    {p : ℕ} (hp : p.Prime) (P : Sylow p (pairPointStabilizer H beta))
    (hPE : (P : Subgroup (pairPointStabilizer H beta)).map
      (pairPointStabilizer H beta).subtype ≤ triplePointStabilizer H z beta) :
    (Nat.card ((CFSG.oddCore (triplePointStabilizer H z beta)).map
      (triplePointStabilizer H z beta).subtype)).factorization p =
        (Nat.card (pairOddCore H beta)).factorization p := by
  obtain ⟨R, hR⟩ := generatedPairGrowth_triple_odd_core_contains_pair_core_sylow
    h S hzS hzcenter hbeta ht hp P hPE
  exact generatedPairGrowth_full_prime_part_of_sylow_contained hp _ _
    (triple_odd_core_le_pair_odd_core h S hzS hzcenter hbeta ht) R hR

end CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
