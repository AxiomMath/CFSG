module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionProperHullThetaGrowth
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureThetaHall

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree

universe u

variable {G : Type u} [Group G] [Finite G]

theorem properHull_minimal_failure_base_triple_centralization
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (K : Type u) [Group K] [Finite K], Nat.card K < Nat.card G →
      2 ≤ twoRank K → (∃ A : Subgroup K, fusionStronglyEmbedded A) → R1Full K)
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1) :
    triplePointStabilizer H z beta =
      pairPointStabilizer H beta ⊓ Subgroup.centralizer ({z} : Set G) := by
  by_contra hnoncentral
  obtain ⟨p, hp, hpodd, P, t, ht, hPz, hnoncentralP, htP, hrank, _hstrict, hnonHall⟩ :=
    properHull_noncentral_triple_nonHall_witness h hcomm hsmallerR1 beta hbeta hnoncentral
  exact hnonHall (minimalLocalFailure_theta_core_Hall_subgroup
    h hcomm hsmallerR1 beta hbeta p hp hpodd P hPz hnoncentralP t ht htP hrank).2.2

theorem properHull_minimal_failure_distinguished_triple_centralization
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (K : Type u) [Group K] [Finite K], Nat.card K < Nat.card G →
      2 ≤ twoRank K → (∃ A : Subgroup K, fusionStronglyEmbedded A) → R1Full K) :
    distinguishedTripleCentralization H z :=
  properHull_distinguished_triple_of_base h.local_datum
    (fun beta hbeta =>
      properHull_minimal_failure_base_triple_centralization h hcomm hsmallerR1 beta hbeta)

end CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull
