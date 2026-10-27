module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorOddKernelFull

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
open CFSG.BenderSuzuki.PFAppendixIII

universe v

variable {G : Type v} [Group G]

theorem order_two_iff_isInvolution (x : G) : orderOf x = 2 ↔ IsInvolution x := by
  exact (orderOf_eq_prime_iff (p := 2) (x := x)).trans and_comm

@[expose] def rankTwoCentralizerKernelData (H : Subgroup G) (z u : G) : Prop :=
  let M := Subgroup.centralizer ({u} : Set G)
  let L := localInvolutionPointHull z u
  let R := CFSG.oddCore L
  let K := (Subgroup.centralizer (L : Set G)).subgroupOf M
  letI := originalCentralizerFixedSetAction H u
  R ≤ Subgroup.center L ∧ Odd (Nat.card R) ∧
    (∀ k : M, k ∈ K → ∀ a : elementFixedSet H u, k • a = a) ∧
    {x : G | x ∈ M ∧ x ∈ Subgroup.centralizer (L : Set G) ∧ orderOf x = 2} = {u} ∧
    (originalCentralizerHullQuotientConjugation z u).ker = K ∧
    (∀ x : M, orderOf x = 2 →
      originalCentralizerHullQuotientConjugation z u x ∈
        innerAutomorphismSubgroup (L ⧸ R)) ∧
    u ∉ L ∧
    {x : G | x ∈ M ∧ orderOf x = 2} =
      ({u} : Set G) ∪ {x : G | x ∈ L ∧ orderOf x = 2} ∪
        ((fun x : G => u * x) '' {x : G | x ∈ L ∧ orderOf x = 2}) ∧
    Disjoint ({u} : Set G) {x : G | x ∈ L ∧ orderOf x = 2} ∧
    Disjoint ({u} : Set G)
      ((fun x : G => u * x) '' {x : G | x ∈ L ∧ orderOf x = 2}) ∧
    Disjoint {x : G | x ∈ L ∧ orderOf x = 2}
      ((fun x : G => u * x) '' {x : G | x ∈ L ∧ orderOf x = 2})

variable [Finite G]

theorem original_rank_two_centralizer_kernel_data
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
    rankTwoCentralizerKernelData H z u := by
  let M := Subgroup.centralizer ({u} : Set G)
  let L := localInvolutionPointHull z u
  let := originalCentralizerFixedSetAction H u
  have hcores := original_centralizer_rank_two_retained_odd_cores
    h hcomm hsmallerR1 u hu huz hescape hrank
  have hkernel := originalCentralizerHullQuotientConjugation_ker
    h hcomm hsmallerR1 u hu huz hescape hrank
  have hwhole := original_minimal_failure_pair_whole_kernel
    h beta hbeta hpairRank.le u huD hu huz hescape hrank
  have hinner := original_minimal_failure_pair_every_involution_inner
    h beta hbeta hpairRank.le u huD hu huz hescape hrank
  have hpartition := original_minimal_failure_pair_centralizer_involution_partition
    h beta hbeta hpairRank.le u huD hu huz hescape hrank
  unfold rankTwoCentralizerKernelData
  simp only [order_two_iff_isInvolution]
  exact ⟨hcores.2.2.2.1, hcores.2.2.2.2.1, hwhole.2.2.2.1,
    hwhole.2.2.2.2.1, hkernel, hinner, hpartition.1,
    hpartition.2.2.1, hpartition.2.2.2⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull
