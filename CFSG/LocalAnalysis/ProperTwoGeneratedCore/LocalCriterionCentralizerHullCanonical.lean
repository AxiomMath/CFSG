module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerHullCanonicalLiteralSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerHullCanonicalOrbits
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerHullCanonicalRoot

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

universe v

variable {G : Type v} [Group G] [Finite G]

@[expose] def rankTwoCentralizerHullInvolutionsAndLocalOrbits
    (H : Subgroup G) (z u : G) : Prop :=
  rankTwoCentralizerKernelData H z u ∧ rankTwoCentralizerRootData H z u ∧
    rankTwoCentralizerSylowData H z u ∧ rankTwoCentralizerOrbitData H z u ∧
    rankTwoCentralizerLiteralSylowData H z u

theorem unique_rank_two_centralizer_hull_involutions_and_local_orbits
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type v) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (hpairRank : twoRank (pairPointStabilizer H beta) = 1)
    (u : G) (huD : u ∈ pairPointStabilizer H beta)
    (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (hrank : 2 ≤ twoRank (localInvolutionPointHull z u)) :
    rankTwoCentralizerHullInvolutionsAndLocalOrbits H z u := by
  exact ⟨original_rank_two_centralizer_kernel_data
      h hcomm hsmallerR1 beta hbeta hpairRank u huD hu huz hescape hrank,
    original_rank_two_centralizer_root_data h hcomm hsmallerR1
      u (pairPointStabilizer_le_point H beta huD) hu huz hescape hrank,
    original_rank_two_centralizer_sylow_data
      h hcomm hsmallerR1 beta hbeta hpairRank u huD hu huz hescape hrank,
    original_rank_two_centralizer_orbit_data
      h hcomm hsmallerR1 beta hbeta hpairRank u huD hu huz hescape hrank,
    original_rank_two_centralizer_literal_sylow_data
      h hcomm hsmallerR1 beta hbeta hpairRank u huD hu huz hescape hrank⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull
