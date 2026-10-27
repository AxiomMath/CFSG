module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCentralizerSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionProperHullDatum
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionProperHullTheta
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionProperHullThetaTransport

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

universe u

variable {G : Type u} [Group G]

theorem properHull_normalized_pair_subgroup_le_triple
    (H : Subgroup G) (s : G) (delta : pointRightCosetSpace H)
    (A : Subgroup G) (hAD : A ≤ pairPointStabilizer H delta)
    (hsA : s ∈ Subgroup.normalizer (A : Set G)) :
    A ≤ triplePointStabilizer H s delta := by
  intro a ha
  refine ⟨hAD ha, ?_⟩
  apply (mem_rightCosetStabilizer_iff H (rightCosetTranslate H delta s) a).mpr
  have hconj : s * a * s⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hsA a).mp ha
  have hfix : rightCosetTranslate H delta (s * a * s⁻¹) = delta :=
    (mem_rightCosetStabilizer_iff H delta _).mp (hAD hconj).2
  calc
    rightCosetTranslate H (rightCosetTranslate H delta s) a =
        rightCosetTranslate H delta (s * a) := rightCosetTranslate_mul H _ _ _
    _ = rightCosetTranslate H (rightCosetTranslate H delta (s * a * s⁻¹)) s := by
      rw [rightCosetTranslate_mul]
      simp only [mul_assoc, inv_mul_cancel, mul_one]
    _ = rightCosetTranslate H delta s := by rw [hfix]

variable [Finite G]

theorem properHull_theta_prescribed_centralizer_sylow_contradiction
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hFR : ∀ (K : Type u) [Group K] [Finite K], Nat.card K < Nat.card G →
      2 ≤ twoRank K → (∃ A : Subgroup K, fusionStronglyEmbedded A) → R1Full K)
    (hdoubly : ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hqodd : Odd q)
    (X : Subgroup G) (hXH : X ≤ H)
    (hXz : rightConjugate X z = X)
    (hnoncentral : ¬ X ≤ Subgroup.centralizer ({z} : Set G))
    (hescape : ¬ Subgroup.normalizer (X : Set G) ≤ H)
    (hrank : 2 ≤ CFSG.Open.pRank 2
      (properHull (Subgroup.normalizer (X : Set G)) z))
    (delta : numeratorRightOrbit H (Subgroup.normalizer (X : Set G)) (rightCosetMk H 1))
    (hdelta : delta.val ≠ rightCosetMk H 1)
    (QG : Subgroup G) (hQ : IsPGroup q QG) (hQne : QG ≠ ⊥)
    (hQC : QG ≤ minimalLocalFailurePairConfinementTheta p
      (pairPointStabilizer H delta.val))
    (hQX : QG ≤ Subgroup.centralizer (X : Set G))
    (hqE : ¬ q ∣ Nat.card (minimalLocalFailurePairConfinementTheta p
      (triplePointStabilizer H z beta))) : False := by
  let C := pairPointStabilizer H delta.val ⊓ Subgroup.centralizer (X : Set G)
  have hQCfull : QG ≤ C := le_inf
    (hQC.trans (pairConfinement_theta_le p (pairPointStabilizer H delta.val))) hQX
  have hQinternal : IsPGroup q (QG.subgroupOf C) := hQ.of_injective
    (Subgroup.subgroupOfEquivOfLe hQCfull).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hQCfull).injective
  obtain ⟨A, hQA⟩ := hQinternal.exists_le_sylow
  let AG := (A : Subgroup C).map C.subtype
  have hQAG : QG ≤ AG := by
    have hm := Subgroup.map_mono (f := C.subtype) hQA
    rw [Subgroup.map_subgroupOf_eq_of_le hQCfull] at hm
    exact hm
  obtain ⟨s, hsH, _hsX, hsA, _hsProduct⟩ :=
    minimalLocalFailure_centralizer_sylow_involution_normalizer h hFR X hXH hXz
      hnoncentral hescape hrank delta hdelta q hq hqodd A
  have hAD : AG ≤ pairPointStabilizer H delta.val :=
    (Subgroup.map_subtype_le _).trans inf_le_left
  have hAE := properHull_normalized_pair_subgroup_le_triple H s delta.val AG hAD hsA
  have hsclass : s ∈ involutionPointClass z := by
    obtain ⟨a, ha⟩ := hsH
    exact ⟨(a : G), ha⟩
  have hsHmem : s ∈ H := by
    obtain ⟨a, ha⟩ := hsH
    rw [← ha]
    exact H.mul_mem (H.mul_mem (H.inv_mem a.property) h.local_datum.distinguished_mem)
      a.property
  have hsfix : pointRightCosetMul H (rightCosetMk H 1) s = rightCosetMk H 1 :=
    (point_right_base_fixed_iff H s).mpr hsHmem
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  have hcard := properHull_distinguished_triple_theta_card h.local_datum S hzS hzcenter
    hdoubly p beta hbeta s hsclass (rightCosetMk H 1) delta.val hsfix hdelta
  have hqEs : ¬ q ∣ Nat.card (minimalLocalFailurePairConfinementTheta p
      (triplePointStabilizer H s delta.val)) := by
    change ¬ q ∣ Nat.card (minimalLocalFailurePairConfinementTheta p
      ((rightCosetStabilizer H (rightCosetMk H 1) ⊓ rightCosetStabilizer H delta.val) ⊓
        rightCosetStabilizer H (rightCosetTranslate H delta.val s)))
    rw [← pointRightCosetMul_eq_translate, hcard]
    exact hqE
  have hQE := properHull_pGroup_inf_theta_eq_bot p q hp hq
    (pairPointStabilizer H delta.val) (triplePointStabilizer H s delta.val) QG
    inf_le_left hQ hQC hqEs
  exact hQne (le_bot_iff.mp (hQE ▸ le_inf le_rfl (hQAG.trans hAE)))

end CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull
