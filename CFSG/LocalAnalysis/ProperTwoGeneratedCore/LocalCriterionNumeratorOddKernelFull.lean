module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionProperHullTripleCentralization
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairQuotient
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorOddKernel

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

universe u

variable {G : Type u} [Group G] [Finite G]

theorem original_centralizer_rank_two_retained_odd_cores
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (K : Type u) [Group K] [Finite K], Nat.card K < Nat.card G →
      2 ≤ twoRank K → (∃ A : Subgroup K, fusionStronglyEmbedded A) → R1Full K)
    (u : G) (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (hrank : 2 ≤ twoRank (localInvolutionPointHull z u)) :
    let L := localInvolutionPointHull z u
    let M := Subgroup.centralizer ({u} : Set G)
    let R := properOddCore M
    R ≤ H ∧ ⁅R, L⁆ = ⊥ ∧ properOddCore L ≤ R ∧
      CFSG.oddCore L ≤ Subgroup.center L ∧
      Odd (Nat.card (CFSG.oddCore L)) ∧ CFSG.oddCore L ≤ H.subgroupOf L :=
  original_centralizer_rank_two_retained_odd_cores_of_triple h
    (properHull_minimal_failure_distinguished_triple_centralization h hcomm hsmallerR1)
    u hu huz hescape hrank

theorem original_local_hull_entire_oddCore_central
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (K : Type u) [Group K] [Finite K], Nat.card K < Nat.card G →
      2 ≤ twoRank K → (∃ A : Subgroup K, fusionStronglyEmbedded A) → R1Full K)
    (u : G) (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (hrank : 2 ≤ twoRank (localInvolutionPointHull z u)) :
    CFSG.oddCore (localInvolutionPointHull z u) ≤
      Subgroup.center (localInvolutionPointHull z u) :=
  (original_centralizer_rank_two_retained_odd_cores h hcomm hsmallerR1
    u hu huz hescape hrank).2.2.2.1

theorem originalCentralizerHullQuotientConjugation_ker
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (K : Type u) [Group K] [Finite K], Nat.card K < Nat.card G →
      2 ≤ twoRank K → (∃ A : Subgroup K, fusionStronglyEmbedded A) → R1Full K)
    (u : G) (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (hrank : 2 ≤ twoRank (localInvolutionPointHull z u)) :
    (originalCentralizerHullQuotientConjugation z u).ker =
      (Subgroup.centralizer (localInvolutionPointHull z u : Set G)).subgroupOf
        (Subgroup.centralizer ({u} : Set G)) :=
  originalCentralizerHullQuotientConjugation_ker_of_central_oddCore h.local_datum u
    (original_local_hull_entire_oddCore_central h hcomm hsmallerR1 u hu huz hescape hrank)

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
