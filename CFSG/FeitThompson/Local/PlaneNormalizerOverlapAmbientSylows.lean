module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.PlaneNormalizerOverlapFrattini
import CFSG.FeitThompson.Local.PlaneNormalizerRankTwoPrimesInSigma
import CFSG.FeitThompson.Local.NonabelianAmbientUniqueNonregularLine
import CFSG.FeitThompson.Local.NonabelianAmbientNormalHallFreeComplement
import CFSG.FeitThompson.Local.SigmaPrimeNormalizerOutsideComplement
import CFSG.FeitThompson.Local.AbelianHallTauTwoControlsCentralizers
import CFSG.FeitThompson.Local.SigmaPrimeNormalizerEmbeddingSylows
import CFSG.FeitThompson.Local.KappaPairMixedDensity
import CFSG.FeitThompson.Local.NonabelianAmbientPlaneCentralizer
import CFSG.FeitThompson.Local.KappaResidualInPrescribedComplement
import CFSG.FeitThompson.Local.KappaDerivedComplement
import CFSG.FeitThompson.Local.NilpotentSigmaPrimeSeparation
import CFSG.FeitThompson.Local.ThreePrimeComplementDecomposition
import CFSG.FeitThompson.Local.SigmaCoreNormalHallDerived
import CFSG.FeitThompson.Local.PrimeFreeFactorizationFixedSubgroupTransport
import CFSG.FeitThompson.Local.RankThreeNormalAbelianSelfCentralizing
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

open Subgroup CFSG.FeitThompson

universe u

variable {G : Type*} [Group G]

theorem eq_bot_of_le_of_isPGroup_of_coprime [Finite G] {q : ℕ} (hq : q.Prime) {K Y : Subgroup G}
    (hYK : Y ≤ K) (hKq : IsPGroup q ↥K) (hcop : Nat.Coprime q (Nat.card ↥Y)) : Y = ⊥ := by
  have := Fact.mk hq
  obtain ⟨n, hn⟩ := hKq.exists_card_eq
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hq).1 (hn ▸ Subgroup.card_dvd_of_le hYK)
  match k, hk with
  | 0, hk => exact Subgroup.card_eq_one.1 (by simpa using hk)
  | (k + 1), hk =>
    exact absurd (hcop.eq_one_of_dvd (by rw [hk]; exact dvd_pow_self q k.succ_ne_zero))
      hq.one_lt.ne'

theorem FNI_plane_normalizer_overlap_ambient_sylows
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_tau_two_hall_abelian.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_nonabelian_ambient_prime_kernel_complement.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FNI_plane_normalizer_overlap_prime_maximum.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FPL_low_rank_sylow_central_product.{u})
    (h₉ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u}) :
    _root_.CFSG.FeitThompson.Statements.FNI_plane_normalizer_overlap_ambient_sylows.{u} := by
  intro G _ _ hG p M A E T hosp hsc hAE hT hNT q hq hqidx hqcard
  have hp : p.Prime := hosp.prime
  have := hG.isSimpleGroup
  have hqf := Fact.mk hq
  have hFin : Fintype G := Fintype.ofFinite G
  have hG03 : CFSG.FeitThompson.Prep03.IsAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG08 : CFSG.FeitThompson.Prep08.IsMinimalSimpleOddOrder G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
  set C : Subgroup G := E ⊓ centralizer (A : Set G) with hCdef
  have hCE : C ≤ E := inf_le_left
  obtain ⟨x, hxC, hxord⟩ := exists_mem_orderOf_eq_of_dvd hq hqcard
  set Q₀ : Subgroup G := zpowers x with hQ₀def
  have hQ₀C : Q₀ ≤ C := zpowers_le.2 hxC
  have hQ₀card : Nat.card Q₀ = q := by rw [hQ₀def, Nat.card_zpowers, hxord]
  obtain ⟨hqτT, hQ₀T⟩ :=
    h₇ G hG p M A E T hosp hsc hAE hT hNT q hq hqidx hqcard Q₀ hQ₀C hQ₀card
  have hqσT : q ∉ sigmaPrimes T := (mem_tauTwoPrimes_iff.1 hqτT).2.1
  have hqrankT : elementaryAbelianPRank q ↥T = 2 := (mem_tauTwoPrimes_iff.1 hqτT).2.2
  obtain ⟨B', hB'T, hB'plane⟩ := exists_isPlaneAt_le_of_elementaryAbelianPRank_eq_two hq hqrankT
  obtain ⟨hnilT, -, -⟩ := h₉ G hG08 T B' q hT hq hqσT hB'T hB'plane
  obtain ⟨hrankM, -, -, -⟩ := h₆ G hG p M A hosp
  obtain ⟨-, hτ₂σ⟩ :=
    FNI_plane_normalizer_rank_two_primes_in_sigma h₁ h₂ h₄ h₅ h₆ h₉ G hG p M A E T
      hosp hsc hAE hT hNT
  have hpσT : p ∈ sigmaPrimes T :=
    hτ₂σ (mem_tauTwoPrimes_iff.2 ⟨hp, hosp.notMem_sigmaPrimes, hrankM⟩)
  obtain ⟨P, hPcard, hPnorm⟩ := exists_normalizer_eq_of_mem_sigmaPrimes_of_isNilpotent
    hG.not_isMulCommutative hG.odd_natCard hG.isSolvable_of_ne_top hT hnilT hpσT
  have hfirst : ∃ P : Subgroup G, _root_.CFSG.FeitThompson.IsSylowSubgroup p P ∧ P ≤ T ∧
      T ≤ normalizer (P : Set G) :=
    ⟨P, (_root_.CFSG.FeitThompson.isSylowSubgroup_iff_natCard hp).2 hPcard,
      hPnorm ▸ Subgroup.le_normalizer, hPnorm.ge⟩
  have hQ₀E : Q₀ ≤ E := hQ₀C.trans hCE
  have hQ₀p : IsPGroup q ↥Q₀ := IsPGroup.of_card (n := 1) (by rw [hQ₀card, pow_one])
  obtain ⟨S, hS⟩ := (hQ₀p.of_equiv (subgroupOfEquivOfLe hQ₀E).symm).exists_le_sylow
  set Q : Subgroup G := (S : Subgroup ↥E).map E.subtype with hQdef
  have hQ₀Q : Q₀ ≤ Q := fun y hy =>
    ⟨⟨y, hQ₀E hy⟩, hS (show (⟨y, hQ₀E hy⟩ : ↥E) ∈ Q₀.subgroupOf E from hy), rfl⟩
  have hQsyl : _root_.CFSG.FeitThompson.IsSylowIn q E Q := ⟨S, rfl⟩
  have hQcardE : Nat.card Q = q ^ (Nat.card ↥E).factorization q := by
    rw [hQdef, Subgroup.card_subtype]; exact S.card_eq_multiplicity
  obtain ⟨-, hQcyc, -, -, -, -, -⟩ :=
    FNI_plane_normalizer_overlap_frattini h₁ h₂ h₄ h₆ G hG p M A E T hosp hsc hAE hT hNT q hq
      hqidx hqcard Q₀ Q hQ₀C hQ₀card hQsyl hQ₀Q
  have := hQcyc
  have hQabel : IsMulCommutative ↥Q := inferInstance
  have hQT : Q ≤ T :=
    (le_centralizer_of_isMulCommutative_of_le hQabel hQ₀Q).trans
      ((centralizer_le_normalizer _).trans hQ₀T)
  have habel : ∀ R : Subgroup G, _root_.CFSG.FeitThompson.IsSylowSubgroup q R → IsMulCommutative ↥R := by
    intro R hR
    by_contra hRnc
    have hQpi : IsPiSubgroup ((sigmaPrimes T)ᶜ) Q := by
      refine isPiSubgroup_iff.2 fun r hr => ?_
      obtain ⟨hrp, hrd, -⟩ := Nat.mem_primeFactors.1 hr
      rw [hQcardE] at hrd
      exact (Nat.prime_dvd_prime_iff_eq hrp hq).1 (hrp.dvd_of_dvd_pow hrd) ▸ hqσT
    obtain ⟨F, hQF, hFsemi⟩ := exists_isInternalSemidirectProduct_sigmaCore_ge
      hG.not_isMulCommutative hG.odd_natCard hG.isSolvable_of_ne_top hT hQT hQpi
    have hFT : F ≤ T := hFsemi.right_le
    have hFhall : IsHallSubgroup ((sigmaPrimes T)ᶜ) (F.subgroupOf T) :=
      isHallSubgroup_subgroupOf_of_isInternalSemidirectProduct
        (isHallSubgroup_subgroupOf_sigmaCore hG.not_isMulCommutative hG.odd_natCard
          hG.isSolvable_of_ne_top hT) hFsemi
    have hfac : (Nat.card ↥F).factorization q = (Nat.card ↥T).factorization q :=
      factorization_eq_of_isHallPiSubgroup hq hqσT hFT hFhall.isHallPiSubgroup
    obtain ⟨P₁, hQP₁, hP₁⟩ := exists_isSylowSubgroupOf_ge hq hQF (IsPGroup.of_card hQcardE)
    have hP₁T : P₁ ≤ T := hP₁.1.trans hFT
    have hP₁card : Nat.card ↥P₁ = q ^ (Nat.card ↥T).factorization q := by rw [hP₁.2, hfac]
    obtain ⟨B, hBP₁, hBelem, hBcard⟩ :=
      exists_isElementaryAbelian_natCard_eq_sq_le_of_isSylow hq hP₁T hP₁card hqrankT
    have hBF : B ≤ F := hBP₁.trans hP₁.1
    have hBT : B ≤ T := hBF.trans hFT
    have hBplane : _root_.CFSG.FeitThompson.IsOutsideSigmaPlane q T B :=
      ⟨hT, hq, hqσT, hBT, nonempty_mulEquiv_pi_of_isElementaryAbelian hq hBelem hBcard⟩
    have hFsc : _root_.CFSG.FeitThompson.IsSigmaComplement T F := ⟨hT, hFsemi⟩
    obtain ⟨B₀, -, -, -, hlines, hB₀eq, -, -⟩ :=
      FNI_nonabelian_ambient_unique_nonregular_line h₁ h₄ h₅ h₆ h₈ h₉ G hG q T B F hBplane hFsc
        hBF ⟨R, hR, hRnc⟩
    have hQ₀F : Q₀ ≤ F := hQ₀Q.trans hQF
    have hQ₀B₀ : Q₀ = B₀ := by
      by_contra hne
      exact (hlines Q₀ hQ₀F hQ₀card hne).2 ((centralizer_le_normalizer _).trans hQ₀T)
    have hsetup : CFSG.FeitThompson.Prep03.IsPlaneSetup G q T B F :=
      ⟨hG03, hT, hq, hqσT, hBT, hBplane.isElementaryAbelianPlane,
        ⟨hFsemi.left_le, hFsemi.right_le, hFsemi.le_normalizer, hFsemi.sup_eq,
          disjoint_iff.1 hFsemi.disjoint⟩, hBF⟩
    obtain ⟨-, -, -, -, F₀, hF₀semi, -, -⟩ :=
      h₃ G hG03 q T B F hsetup
        ⟨R, (_root_.CFSG.FeitThompson.isSylowSubgroup_iff_natCard hq).1 hR, hRnc⟩ Q₀
        (by rw [hQ₀B₀, hB₀eq]; rfl)
    have hQsemi : CFSG.FeitThompson.Prep03.IsSemidirect Q Q₀ (Q ⊓ F₀) :=
      isSemidirect_inf_of_le hF₀semi hQ₀Q hQF
    have hcop : (Nat.card ↥Q₀).Coprime (Nat.card ↥(Q ⊓ F₀)) :=
      coprime_natCard_of_isCyclic_of_inf_eq_bot (Z := Q) hQ₀Q inf_le_left hQsemi.2.2.2.2
    have hQF₀bot : Q ⊓ F₀ = ⊥ :=
      eq_bot_of_le_of_isPGroup_of_coprime hq inf_le_left (IsPGroup.of_card hQcardE)
        (by rwa [hQ₀card] at hcop)
    have hQeq : Q = Q₀ := by
      have h1 := hQsemi.2.2.2.1
      rw [hQF₀bot, sup_bot_eq] at h1
      exact h1.symm
    have hdvd1 : q ^ (Nat.card ↥E).factorization q ∣ Nat.card ↥C := by
      rw [← hQcardE]; exact Subgroup.card_dvd_of_le (hQeq ▸ hQ₀C)
    have hdvd2 : q ^ ((Nat.card ↥E).factorization q + 1) ∣ Nat.card ↥E := by
      have hmul := mul_dvd_mul hdvd1 hqidx
      rw [← pow_succ, natCard_mul_relIndex_of_le hCE] at hmul
      exact hmul
    have hle := (Nat.Prime.pow_dvd_iff_le_factorization hq (Nat.card_pos (α := ↥E)).ne').1 hdvd2
    omega
  obtain ⟨R, hR⟩ := (IsPGroup.of_card hQcardE).exists_le_sylow
  refine ⟨hfirst, (R : Subgroup G), ⟨R, rfl⟩, habel _ ⟨R, rfl⟩, ?_⟩
  exact (le_centralizer_of_isMulCommutative_of_le (habel _ ⟨R, rfl⟩) (hQ₀Q.trans hR)).trans
    ((centralizer_le_normalizer _).trans hQ₀T)

end

end CFSG.FeitThompson.Proofs
