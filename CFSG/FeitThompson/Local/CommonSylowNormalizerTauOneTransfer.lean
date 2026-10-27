module

public import CFSG.FeitThompson.Statements.FittingOverlapKappaStatements
public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.CommonSylowNormalizerBetaFactor
import CFSG.FeitThompson.Representations.TypeThreeFourCorePrimeGroup
import CFSG.FeitThompson.Local.CoreCentralizerTypeIIIOrIVDerived
import CFSG.FeitThompson.Local.BetaPrimesSigmaCompatibility
import CFSG.FeitThompson.Definitions.TheThreeTauPrimeSets
import CFSG.FeitThompson.Definitions.SigmaPrimesAndSigmaCore
import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps
public import Mathlib

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson Subgroup Pointwise

universe u

variable {G : Type u} [Group G] {r : ℕ}

theorem sup_eq_of_coe_eq_mul_of_le_normalizer {B J K : Subgroup G}
    (hK : (K : Set G) = (B : Set G) * (J : Set G))
    (hn : J ≤ normalizer (B : Set G)) : B ⊔ J = K :=
  SetLike.coe_injective ((Subgroup.coe_mul_of_right_le_normalizer_left B J hn).trans hK.symm)

theorem factorization_natCard_eq_of_sup_eq [Finite G] (hr : r.Prime) {B J K : Subgroup G}
    (hsup : B ⊔ J = K) (hn : J ≤ normalizer (B : Set G)) (hB : ¬ r ∣ Nat.card ↥B) :
    (Nat.card ↥K).factorization r = (Nat.card ↥J).factorization r := by
  have hJK : J ≤ K := hsup ▸ le_sup_right
  have hdvd : Nat.card ↥K ∣ Nat.card ↥B * Nat.card ↥J := hsup ▸ natCard_sup_dvd_mul hn
  refine le_antisymm ?_ ?_
  · refine (hr.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 ?_
    exact (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hr).2 hB)).dvd_of_dvd_mul_left
      ((Nat.ordProj_dvd _ _).trans hdvd)
  · exact (hr.pow_dvd_iff_le_factorization Nat.card_pos.ne').1
      ((Nat.ordProj_dvd _ _).trans (Subgroup.card_dvd_of_le hJK))

theorem exists_le_natCard_eq_pow_factorization [Finite G] (hr : r.Prime) (J : Subgroup G) :
    ∃ R : Subgroup G, R ≤ J ∧ Nat.card ↥R = r ^ (Nat.card ↥J).factorization r := by
  have := Fact.mk hr
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥J) r (Nat.ordProj_dvd _ _)
  exact ⟨K.map J.subtype, Subgroup.map_subtype_le K, by rw [Subgroup.card_subtype, hK]⟩

theorem mem_betaPrimes_of_dvd_natCard_betaCore [Finite G] (hr : r.Prime) (M : Subgroup G)
    (hd : r ∣ Nat.card ↥(betaCore M)) : r ∈ betaPrimes ↥M :=
  isPiSubgroup_iff.1 (isPiSubgroup_betaCore M) r
    (Nat.mem_primeFactors.2 ⟨hr, hd, Nat.card_pos.ne'⟩)

theorem FBG_common_sylow_normalizer_tau_one_transfer
    (h₁ : CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FTS_beta_prime_centralizing_sylow.{u})
    (h₃ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FBG_common_sylow_normalizer_tau_one_transfer.{u} := by
  intro G _ _ hG M T hM hT hMT q hq Q hNQ
  have : Fintype G := Fintype.ofFinite G
  have := hG.isSimpleGroup
  have hG2 : CFSG.FeitThompson.IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  obtain ⟨hHallOf, -, hSMp⟩ := h₁ G hG2 M hM
  obtain ⟨hMfac, hαβ, -, -⟩ :=
    FBG_common_sylow_normalizer_beta_factor h₁ h₂ h₃ G hG M T hM hT hMT q hq Q hNQ
  have hNQ' : normalizer ((Q : Subgroup G) : Set G) ≤ T ⊓ M := by rw [inf_comm]; exact hNQ
  obtain ⟨hTfac, -, -, -⟩ :=
    FBG_common_sylow_normalizer_beta_factor h₁ h₂ h₃ G hG T M hT hM (Ne.symm hMT) q hq Q hNQ'
  rw [inf_comm] at hTfac
  have hJM : (M ⊓ T : Subgroup G) ≤ M := inf_le_left
  have hJT : (M ⊓ T : Subgroup G) ≤ T := inf_le_right
  have hsupM : betaCore M ⊔ (M ⊓ T) = M :=
    sup_eq_of_coe_eq_mul_of_le_normalizer hMfac (hJM.trans (le_normalizer_betaCore M))
  have hsupT : betaCore T ⊔ (M ⊓ T) = T :=
    sup_eq_of_coe_eq_mul_of_le_normalizer hTfac (hJT.trans (le_normalizer_betaCore T))
  intro r hr
  by_cases hrα : r ∈ alphaPrimes ↥M
  · exact Set.mem_union_right _ hrα
  refine Set.mem_union_left _ ?_
  obtain ⟨hrp, hrT, hrσT, hrankT, hrT'⟩ := mem_tau1Primes_iff.1 hr
  have hrBT : ¬ r ∣ Nat.card ↥(betaCore T) := fun hd =>
    hrσT (betaPrimes_subset_sigmaPrimes hG.not_isMulCommutative hG.odd_natCard hG.isSolvable hT
      (mem_betaPrimes_of_dvd_natCard_betaCore hrp T hd))
  have hrBM : ¬ r ∣ Nat.card ↥(betaCore M) := fun hd =>
    hrα (hαβ ▸ mem_betaPrimes_of_dvd_natCard_betaCore hrp M hd)
  have hfacM : (Nat.card ↥M).factorization r = (Nat.card ↥(M ⊓ T : Subgroup G)).factorization r :=
    factorization_natCard_eq_of_sup_eq hrp hsupM (hJM.trans (le_normalizer_betaCore M)) hrBM
  have hfacT : (Nat.card ↥T).factorization r = (Nat.card ↥(M ⊓ T : Subgroup G)).factorization r :=
    factorization_natCard_eq_of_sup_eq hrp hsupT (hJT.trans (le_normalizer_betaCore T)) hrBT
  have hfacpos : 0 < (Nat.card ↥T).factorization r :=
    hrp.factorization_pos_of_dvd Nat.card_pos.ne' hrT
  have hrM : r ∣ Nat.card ↥M := Nat.dvd_of_factorization_pos (by rw [hfacM, ← hfacT]; omega)
  obtain ⟨R, hRJ, hRcard⟩ := exists_le_natCard_eq_pow_factorization hrp (M ⊓ T : Subgroup G)
  have hrankM : elementaryAbelianPRank r ↥M = 1 := by
    have h1 : elementaryAbelianPRank r ↥R = elementaryAbelianPRank r ↥M :=
      elementaryAbelianPRank_eq_of_natCard_eq_pow hrp (hRJ.trans hJM) (by rw [hRcard, ← hfacM])
    have h2 : elementaryAbelianPRank r ↥R = elementaryAbelianPRank r ↥T :=
      elementaryAbelianPRank_eq_of_natCard_eq_pow hrp (hRJ.trans hJT) (by rw [hRcard, ← hfacT])
    rw [← h1, h2, hrankT]
  have hrJ' : ¬ r ∣ Nat.card ↥(⁅(M ⊓ T : Subgroup G), (M ⊓ T : Subgroup G)⁆ : Subgroup G) :=
    fun hd => hrT' (hd.trans (Subgroup.card_dvd_of_le (Subgroup.commutator_mono hJT hJT)))
  have hrM' : ¬ r ∣ Nat.card ↥(⁅M, M⁆ : Subgroup G) := by
    intro hd
    have hle : (⁅M, M⁆ : Subgroup G) ≤ betaCore M ⊔ ⁅(M ⊓ T : Subgroup G), (M ⊓ T : Subgroup G)⁆ :=
      commutator_le_sup_commutator_of_sup (betaCore_le M) hJM hsupM (le_normalizer_betaCore M)
    have hdvd : Nat.card ↥(⁅M, M⁆ : Subgroup G) ∣
        Nat.card ↥(betaCore M) *
          Nat.card ↥(⁅(M ⊓ T : Subgroup G), (M ⊓ T : Subgroup G)⁆ : Subgroup G) :=
      (Subgroup.card_dvd_of_le hle).trans (natCard_sup_dvd_mul
        (((Subgroup.commutator_le_self _).trans hJM).trans (le_normalizer_betaCore M)))
    rcases (Nat.Prime.dvd_mul hrp).1 (hd.trans hdvd) with h | h
    · exact hrBM h
    · exact hrJ' h
  have hrσM : r ∉ sigmaPrimes M := by
    intro hmem
    have hfac := factorization_natCard_eq_of_isHallPiSubgroup_subgroupOf hrp (sigmaCore_le M)
      hHallOf.2 hmem
    have hdvdS : r ∣ Nat.card ↥(sigmaCore M) := Nat.dvd_of_factorization_pos (by
      rw [← hfac]
      exact (hrp.factorization_pos_of_dvd Nat.card_pos.ne' hrM).ne')
    exact hrM' (hdvdS.trans (Subgroup.card_dvd_of_le hSMp))
  exact mem_tau1Primes_iff.2 ⟨hrp, hrM, hrσM, hrankM, hrM'⟩

end

end CFSG.FeitThompson.Proofs
