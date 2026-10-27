module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionProperHullThetaContradiction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionProperHullThetaSecondPair

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

universe u

variable {G : Type u} [Group G] [Finite G]

theorem properHull_original_sylow_theta_prime_contradiction
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hFR : ∀ (K : Type u) [Group K] [Finite K], Nat.card K < Nat.card G →
      2 ≤ twoRank K → (∃ A : Subgroup K, fusionStronglyEmbedded A) → R1Full K)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (P : Sylow p ((CFSG.oddCore (triplePointStabilizer H z beta)).map
      (triplePointStabilizer H z beta).subtype))
    (hzP : z ∈ Subgroup.normalizer
      (((P : Subgroup ((CFSG.oddCore (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype)).map
          ((CFSG.oddCore (triplePointStabilizer H z beta)).map
            (triplePointStabilizer H z beta).subtype).subtype : Subgroup G) : Set G))
    (hnoncentral : ¬ (P : Subgroup ((CFSG.oddCore (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype)).map
      ((CFSG.oddCore (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype).subtype ≤
          Subgroup.centralizer ({z} : Set G))
    (hMproper : Subgroup.normalizer
      (((P : Subgroup ((CFSG.oddCore (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype)).map
          ((CFSG.oddCore (triplePointStabilizer H z beta)).map
            (triplePointStabilizer H z beta).subtype).subtype : Subgroup G) : Set G) ≠ ⊤)
    (hMescape : ¬ Subgroup.normalizer
      (((P : Subgroup ((CFSG.oddCore (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype)).map
          ((CFSG.oddCore (triplePointStabilizer H z beta)).map
            (triplePointStabilizer H z beta).subtype).subtype : Subgroup G) : Set G) ≤ H)
    (hMrank : 2 ≤ CFSG.Open.pRank 2 (properHull (Subgroup.normalizer
      (((P : Subgroup ((CFSG.oddCore (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype)).map
          ((CFSG.oddCore (triplePointStabilizer H z beta)).map
            (triplePointStabilizer H z beta).subtype).subtype : Subgroup G) : Set G)) z))
    (q : ℕ) (hq : q.Prime) (hqodd : Odd q)
    (hqB : q ∣ Nat.card (minimalLocalFailurePairConfinementTheta p
      (pairPointStabilizer H beta)))
    (hqE : ¬ q ∣ Nat.card (minimalLocalFailurePairConfinementTheta p
      (triplePointStabilizer H z beta))) : False := by
  let : Fact p.Prime := ⟨hp⟩
  let E := triplePointStabilizer H z beta
  let V := (CFSG.oddCore E).map E.subtype
  let U := (P : Subgroup V).map V.subtype
  let X := ⁅U, Subgroup.zpowers z⁆
  have hUp : IsPGroup p U := P.isPGroup'.map V.subtype
  have hUodd : Odd (Nat.card U) := by
    obtain ⟨n, hn⟩ := hUp.exists_card_eq
    rw [hn]
    exact hpodd.pow
  have hUE : U ≤ E := (Subgroup.map_subtype_le _).trans (Subgroup.map_subtype_le _)
  obtain ⟨hXU, hXne, hXp, hXnorm, hself⟩ := properHull_odd_involution_commutator
    p U z hUp hUodd h.local_datum.distinguished_order hzP hnoncentral
  have hXE : X ≤ E := hXU.trans hUE
  have hXH : X ≤ H := by
    have hXbase : X ≤ rightCosetStabilizer H (rightCosetMk H 1) :=
      hXE.trans (inf_le_left.trans inf_le_left)
    rw [rightCosetStabilizer_base] at hXbase
    exact hXbase
  have hzX : z ∈ Subgroup.normalizer (X : Set G) :=
    hXnorm (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
  have hdoubly := (minimalLocalFailureSylowFixedPointsFromProperCommutingImages h hcomm).2.2.1
  obtain ⟨R, _hRne, _hRH, _hXR, _hRX, hXescape⟩ :=
    properHull_theta_opposite_normalizer_escape h.local_datum hdoubly beta hbeta
      p q hp hq X hXp hXE hzX hself hqB hqE
  have hXz : rightConjugate X z = X :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.normalizer (X : Set G)).inv_mem hzX)
  have hXnoncentral := properHull_self_commutator_noncentral X z hXne hself
  have hXrank := properHull_commutator_normalizer_hull_rank h U hzP
    (lt_top_iff_ne_top.mpr hMproper) hMescape hMrank hXescape
  obtain ⟨d, hd, hdH⟩ := IsConcreteLE.not_le_iff_exists.mp hXescape
  let delta : numeratorRightOrbit H (Subgroup.normalizer (X : Set G)) (rightCosetMk H 1) :=
    ⟨pointRightCosetMul H (rightCosetMk H 1) d, d, hd, rfl⟩
  have hdelta : delta.val ≠ rightCosetMk H 1 := by
    intro heq
    exact hdH ((point_right_base_fixed_iff H d).mp heq)
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  obtain ⟨Q, hQne, hQp, hQC, hQX⟩ := properHull_theta_second_pair_centralizing_sylow
    h.local_datum S hzS hzcenter hdoubly beta hbeta p q hp hq X hXp hXH hzX hself
      hXescape delta hdelta hqB hqE
  exact properHull_theta_prescribed_centralizer_sylow_contradiction h hFR hdoubly
    beta hbeta p q hp hq hqodd X hXH hXz hXnoncentral hXescape hXrank delta hdelta
      _ hQp hQne hQC hQX hqE

end CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull
