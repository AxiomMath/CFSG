module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionProperHullThetaAssembly
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureStrictThetaGrowth
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureNoncentralSylow

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

universe u

variable {G : Type u} [Group G] [Finite G]

theorem properHull_original_sylow_hall_contradiction
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hFR : ∀ (K : Type u) [Group K] [Finite K], Nat.card K < Nat.card G →
      2 ≤ twoRank K → (∃ A : Subgroup K, fusionStronglyEmbedded A) → R1Full K)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (P : Sylow p ((CFSG.oddCore (triplePointStabilizer H z beta)).map
      (triplePointStabilizer H z beta).subtype))
    (hPz : rightConjugate ((P : Subgroup ((CFSG.oddCore
        (triplePointStabilizer H z beta)).map
          (triplePointStabilizer H z beta).subtype)).map
      ((CFSG.oddCore (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype).subtype) z =
      (P : Subgroup ((CFSG.oddCore (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype)).map
          ((CFSG.oddCore (triplePointStabilizer H z beta)).map
            (triplePointStabilizer H z beta).subtype).subtype)
    (hnoncentral : ¬ (P : Subgroup ((CFSG.oddCore (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype)).map
      ((CFSG.oddCore (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype).subtype ≤
          Subgroup.centralizer ({z} : Set G))
    (t : G) (ht : t ∈ rightPairFlipFiber H z beta)
    (htP : t ∈ Subgroup.normalizer
      (((P : Subgroup ((CFSG.oddCore (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype)).map
          ((CFSG.oddCore (triplePointStabilizer H z beta)).map
            (triplePointStabilizer H z beta).subtype).subtype : Subgroup G) : Set G))
    (hrank : 2 ≤ CFSG.Open.pRank 2 (properHull (Subgroup.normalizer
      (((P : Subgroup ((CFSG.oddCore (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype)).map
          ((CFSG.oddCore (triplePointStabilizer H z beta)).map
            (triplePointStabilizer H z beta).subtype).subtype : Subgroup G) : Set G)) z))
    (hhall : Nat.Coprime
      (Nat.card (minimalLocalFailurePairConfinementTheta p
        (triplePointStabilizer H z beta)))
      ((minimalLocalFailurePairConfinementTheta p (triplePointStabilizer H z beta)).relIndex
        (minimalLocalFailurePairConfinementTheta p (pairPointStabilizer H beta)))) :
    False := by
  let E := triplePointStabilizer H z beta
  let V := (CFSG.oddCore E).map E.subtype
  let U := (P : Subgroup V).map V.subtype
  have hUE : U ≤ E := (Subgroup.map_subtype_le _).trans (Subgroup.map_subtype_le _)
  have hUH : U ≤ H := by
    have hUbase : U ≤ rightCosetStabilizer H (rightCosetMk H 1) :=
      hUE.trans (inf_le_left.trans inf_le_left)
    rw [rightCosetStabilizer_base] at hUbase
    exact hUbase
  have hUne : U ≠ ⊥ := by
    intro hbot
    have hUcentral : U ≤ Subgroup.centralizer ({z} : Set G) := by
      rw [hbot]
      exact bot_le
    exact hnoncentral hUcentral
  have hzU : z ∈ Subgroup.normalizer (U : Set G) :=
    invariant_subgroup_mem_normalizer hPz
  have hMproper := localNormalizer_proper h U hUH hUne
  have htH : t ∉ H := by
    intro htH
    apply hbeta
    calc
      beta = rightCosetTranslate H (rightCosetMk H 1) t := ht.2.symm
      _ = rightCosetMk H 1 := by
        rw [← pointRightCosetMul_eq_translate]
        exact (point_right_base_fixed_iff H t).mpr htH
  have hMescape : ¬ Subgroup.normalizer (U : Set G) ≤ H :=
    fun hle => htH (hle htP)
  have hstrict := (minimalLocalFailure_strict_theta_core_growth
    h hcomm hFR beta hbeta p hp hpodd P hPz hnoncentral t ht htP hrank).1
  obtain ⟨q, hq, hqodd, _hqne, hqB, hqE⟩ := properHull_strict_hall_theta_prime
    p hp (pairPointStabilizer H beta) E hstrict hhall
  exact properHull_original_sylow_theta_prime_contradiction h hcomm hFR
    beta hbeta p hp hpodd P hzU hnoncentral hMproper hMescape hrank q hq hqodd hqB hqE

theorem properHull_noncentral_triple_nonHall_witness
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hFR : ∀ (K : Type u) [Group K] [Finite K], Nat.card K < Nat.card G →
      2 ≤ twoRank K → (∃ A : Subgroup K, fusionStronglyEmbedded A) → R1Full K)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (hnoncentral : triplePointStabilizer H z beta ≠
      pairPointStabilizer H beta ⊓ Subgroup.centralizer ({z} : Set G)) :
    let E := triplePointStabilizer H z beta
    let V := (CFSG.oddCore E).map E.subtype
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ ∃ P : Sylow p V,
      let U := (P : Subgroup V).map V.subtype
      ∃ t : G, t ∈ rightPairFlipFiber H z beta ∧ rightConjugate U z = U ∧
        ¬ U ≤ Subgroup.centralizer ({z} : Set G) ∧
        t ∈ Subgroup.normalizer (U : Set G) ∧
        2 ≤ CFSG.Open.pRank 2 (properHull (Subgroup.normalizer (U : Set G)) z) ∧
        minimalLocalFailurePairConfinementTheta p E <
          minimalLocalFailurePairConfinementTheta p (pairPointStabilizer H beta) ∧
        ¬ Nat.Coprime (Nat.card (minimalLocalFailurePairConfinementTheta p E))
          ((minimalLocalFailurePairConfinementTheta p E).relIndex
            (minimalLocalFailurePairConfinementTheta p (pairPointStabilizer H beta))) := by
  dsimp only
  obtain ⟨_hV, p, hp, hpodd, _hpm, P, _hUne, hUnoncentral, t, ht, hzU, htU,
    _hMproper, _hMescape, hrank, _hlocal, _hovergroups⟩ :=
      minimalLocalFailureNoncentralOddSylowNormalizer h hcomm beta hbeta hnoncentral
  have hUz := rightConjugate_eq_self_of_mem_normalizer hzU
  have hstrict := (minimalLocalFailure_strict_theta_core_growth
    h hcomm hFR beta hbeta p hp hpodd P hUz hUnoncentral t ht htU hrank).1
  refine ⟨p, hp, hpodd, P, t, ht, hUz, hUnoncentral, htU, hrank, hstrict, ?_⟩
  intro hhall
  exact properHull_original_sylow_hall_contradiction h hcomm hFR beta hbeta
    p hp hpodd P hUz hUnoncentral t ht htU hrank hhall

end CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull
