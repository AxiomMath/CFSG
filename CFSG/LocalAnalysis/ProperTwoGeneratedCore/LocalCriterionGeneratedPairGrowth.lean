module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeneratedPairGrowthCanonical
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeneratedPairGrowthHypotheses
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeneratedPairGrowthAdapters
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.OddCorePrimeComplementGrowth

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

open CFSG.ShultStronglyClosedTI CFSG.SignalizerFunctor.Helpers

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

theorem local_involution_point_generated_pair_strict_core_growth
    (hnonabelian : ∃ a b : G, a * b ≠ b * a)
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hgen : (Subgroup.zpowers z ⊔ Subgroup.zpowers t) ⊔ pairOddCore H beta = ⊤)
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (hsylow : ∃ P : Sylow p (pairPointStabilizer H beta),
      (P : Subgroup (pairPointStabilizer H beta)).map
        (pairPointStabilizer H beta).subtype ≤ triplePointStabilizer H z beta) :
    (piCore (generatedPairGrowthCanonicalPrimes p)
        (triplePointStabilizer H z beta)).map (triplePointStabilizer H z beta).subtype <
      (piCore (generatedPairGrowthCanonicalPrimes p)
        (pairPointStabilizer H beta)).map (pairPointStabilizer H beta).subtype ∧
    (piCore (generatedPairGrowthCanonicalPrimes p)
        (pairPointStabilizer H beta)).map (pairPointStabilizer H beta).subtype ≠ ⊥ := by
  obtain ⟨P, hPE⟩ := hsylow
  let J := pairOddCore H beta
  let V := (CFSG.oddCore (triplePointStabilizer H z beta)).map
    (triplePointStabilizer H z beta).subtype
  obtain ⟨hJ, hJodd, hcorefree, hz, hgenN, hVJ, hzV, hpart⟩ :=
    generatedPairGrowth_original_normalizer_growth_hypotheses
      hnonabelian h S hzS hzcenter hbeta ht hgen hp P hPE
  let : Fact p.Prime := ⟨hp⟩
  have hgrowth := odd_core_normalizer_generation_strict_pPrimeCore_growth
    J hJ hJodd hcorefree z hz
    (generatedPairGrowth_normalizer_generation_closure J z hgenN)
    p hpodd V hVJ (generatedPairGrowth_conjugate_eq_of_normalizes V z hzV) hpart
  have hE := generatedPairGrowth_ambient_canonical_core_eq (triplePointStabilizer H z beta) hp
  have hB := generatedPairGrowth_ambient_canonical_core_eq (pairPointStabilizer H beta) hp
  rw [hE, hB]
  exact hgrowth

end CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
