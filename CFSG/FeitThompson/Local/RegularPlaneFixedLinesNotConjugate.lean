module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.RegularFirstPlaneFixedLineEscape
import CFSG.FeitThompson.Local.OutsideSigmaFixedFreeLineCommutator
import CFSG.FeitThompson.Local.KappaNormalizerReflection
import CFSG.FeitThompson.Local.RankThreeNormalAbelianSelfCentralizing
import CFSG.FeitThompson.Local.KappaPrimeLineFixedEquivalence
import CFSG.FeitThompson.Local.FittingOverlapPrimeCoreNoncyclic
import CFSG.FeitThompson.Local.MixedFittingComplementCoreEquality
import CFSG.FeitThompson.Local.ThreePrimeComplementDecomposition
import CFSG.FeitThompson.Local.OutsideSigmaSylowCentralPrimeElement
import CFSG.FeitThompson.Local.SinglePrimeOrbitFixedLine
import CFSG.FeitThompson.Local.PrimeExtensionMaximalInvariantSubgroup
import CFSG.FeitThompson.Foundations.SylowContainmentConjugacy
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

theorem exists_mem_conj_smul_eq_of_natCard_eq_of_elementaryAbelianPRank_le_one
    {G : Type*} [Group G] [Finite G] {q : ℕ} (hq : q.Prime) (hodd : Odd q)
    {M : Subgroup G} (hrank : elementaryAbelianPRank q ↥M ≤ 1)
    {Q₁ Q₂ : Subgroup G} (h₁ : Q₁ ≤ M) (h₂ : Q₂ ≤ M)
    (hc₁ : Nat.card ↥Q₁ = q) (hc₂ : Nat.card ↥Q₂ = q) :
    ∃ m ∈ M, MulAut.conj m • Q₁ = Q₂ := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨S, hScyc⟩ := exists_isCyclic_sylow_of_elementaryAbelianPRank_le_one M hq hodd hrank
  have hpg : ∀ {Y : Subgroup G}, Y ≤ M → Nat.card ↥Y = q → IsPGroup q ↥(Y.subgroupOf M) := by
    intro Y hYM hY
    refine IsPGroup.of_card (n := 1) ?_
    rw [natCard_subgroupOf_of_le' hYM, hY, pow_one]
  obtain ⟨m₁, hm₁, hle₁⟩ := exists_mem_map_conj_le_sylow h₁ (hpg h₁ hc₁) S
  obtain ⟨m₂, hm₂, hle₂⟩ := exists_mem_map_conj_le_sylow h₂ (hpg h₂ hc₂) S
  have hcyc : IsCyclic ↥(Subgroup.map M.subtype (S : Subgroup ↥M)) :=
    isCyclic_sylow_of_exists ⟨S, hScyc⟩ S
  have hcard₁ : Nat.card ↥(Subgroup.map (↑(MulAut.conj m₁) : G →* G) Q₁) = q := by
    rw [Subgroup.card_map_of_injective (MulAut.conj m₁).injective, hc₁]
  have hcard₂ : Nat.card ↥(Subgroup.map (↑(MulAut.conj m₂) : G →* G) Q₂) = q := by
    rw [Subgroup.card_map_of_injective (MulAut.conj m₂).injective, hc₂]
  have heq₀ := eq_of_le_of_natCard_eq_of_isCyclic hle₁ hle₂ (by rw [hcard₁, hcard₂])
  have heq : MulAut.conj m₁ • Q₁ = MulAut.conj m₂ • Q₂ := heq₀
  refine ⟨m₂⁻¹ * m₁, mul_mem (inv_mem hm₂) hm₁, ?_⟩
  calc MulAut.conj (m₂⁻¹ * m₁) • Q₁ = MulAut.conj m₂⁻¹ • (MulAut.conj m₁ • Q₁) := by
        rw [map_mul, mul_smul]
    _ = MulAut.conj m₂⁻¹ • (MulAut.conj m₂ • Q₂) := by rw [heq]
    _ = Q₂ := by rw [← mul_smul, ← map_mul]; simp

theorem FTS_regular_plane_fixed_lines_not_conjugate
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_tau_two_full_central_hall.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_nonabelian_ambient_unique_nonregular_line.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u}) :
    _root_.CFSG.FeitThompson.Statements.FTS_regular_plane_fixed_lines_not_conjugate.{u} := by
  intro G _ _ hG M E A Q D X p q hM hEM hsemi hp hAE hplane hq hQE hQcard hSQ hAQ hDdef hXdef
  subst hDdef
  subst hXdef
  have hsimple : IsSimpleGroup G := hG.isSimpleGroup
  have hG4 : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hpp : p.Prime := prime_of_mem_tauTwoPrimes hp
  have hpσ : p ∉ sigmaPrimes M := notMem_sigmaPrimes_of_mem_tauTwoPrimes hp
  have hqp : q.Prime := prime_of_mem_tau1Primes hq
  have hqσ : q ∉ sigmaPrimes M := notMem_sigmaPrimes_of_mem_tau1Primes hq
  have hAM : A ≤ M := hAE.trans hEM
  have hAcard : Nat.card ↥A = p ^ 2 := hplane.natCard
  have hplane4 : _root_.CFSG.FeitThompson.IsElementaryAbelianPlane p A :=
    nonempty_mulEquiv_pi_of_isElementaryAbelian hpp hplane.isElementaryAbelian hAcard
  have hosp : _root_.CFSG.FeitThompson.IsOutsideSigmaPlane p M A := ⟨hM, hpp, hpσ, hAM, hplane4⟩
  have hsc : _root_.CFSG.FeitThompson.IsSigmaComplement M E := ⟨hM, hsemi⟩
  have hpq : p ≠ q := by
    intro h
    have h2 := elementaryAbelianPRank_eq_two_of_mem_tauTwoPrimes hp
    have h1 := elementaryAbelianPRank_eq_one_of_mem_tau1Primes hq
    rw [h] at h2
    omega
  have hEnormA : E ≤ normalizer (A : Set G) := (h₄ G hG4 p M A E hosp hsc hAE).1
  have hQnormA : Q ≤ normalizer (A : Set G) := hQE.trans hEnormA
  have hDA : (⁅A, Q⁆ : Subgroup G) ≤ A := commutator_le_left_of_le_normalizer hQnormA
  have hDM : (⁅A, Q⁆ : Subgroup G) ≤ M := hDA.trans hAM
  obtain ⟨hDp, hXp, hIDP, hDcent, -⟩ :=
    FNI_regular_first_plane_fixed_line_escape h₁ h₂ h₃ h₄ h₅ h₆ h₇ G hG4 p q M E A Q hsc hp hAE
      hplane4 hq hQE hQcard hSQ hAQ
  obtain ⟨-, -, hMnormD⟩ :=
    FTS_outside_sigma_fixed_free_line_commutator h₁ h₆ h₇ G hG M A Q q hM hqp hqσ hAM
      hplane.isMulCommutative
      (fun s hs hdvd => by
        rw [hAcard] at hdvd
        rw [(Nat.prime_dvd_prime_iff_eq hs hpp).1 (hs.dvd_of_dvd_pow hdvd)]
        exact hpσ)
      (by
        rw [hAcard]
        intro h
        exact hpq ((Nat.prime_dvd_prime_iff_eq hqp hpp).1 (hqp.dvd_of_dvd_pow h)).symm)
      (le_inf hQnormA (hQE.trans hEM)) hQcard hSQ
  have hnormD : normalizer ((⁅A, Q⁆ : Subgroup G) : Set G) = M :=
    normalizer_eq_of_isCoatom hM hAQ hDM hMnormD
  have hCDM : centralizer ((⁅A, Q⁆ : Subgroup G) : Set G) ≤ M :=
    (Subgroup.centralizer_le_normalizer _).trans hnormD.le
  have hqodd : Odd q := by
    refine hG.odd_natCard.of_dvd_nat ?_
    rw [← hQcard]
    exact (Subgroup.card_dvd_of_le le_top).trans (by simp)
  have hrank : elementaryAbelianPRank q ↥M ≤ 1 :=
    le_of_eq (elementaryAbelianPRank_eq_one_of_mem_tau1Primes hq)
  have hqCD : ¬ q ∣ Nat.card ↥(centralizer ((⁅A, Q⁆ : Subgroup G) : Set G)) := by
    intro hdvd
    obtain ⟨x, hxCD, hxord⟩ := exists_mem_orderOf_eq_of_dvd hqp hdvd
    have hQ₀le : zpowers x ≤ centralizer ((⁅A, Q⁆ : Subgroup G) : Set G) := zpowers_le.2 hxCD
    have hQ₀card : Nat.card ↥(zpowers x) = q := by rw [Nat.card_zpowers, hxord]
    obtain ⟨m, hm, hconj⟩ :=
      exists_mem_conj_smul_eq_of_natCard_eq_of_elementaryAbelianPRank_le_one hqp hqodd hrank
        (hQ₀le.trans hCDM) (hQE.trans hEM) hQ₀card hQcard
    have hDfix : MulAut.conj m • (⁅A, Q⁆ : Subgroup G) = ⁅A, Q⁆ :=
      conj_smul_eq_self_iff_mem_normalizer.2 (hnormD ▸ hm)
    have hCfix : MulAut.conj m • centralizer ((⁅A, Q⁆ : Subgroup G) : Set G)
        = centralizer ((⁅A, Q⁆ : Subgroup G) : Set G) := by
      rw [smul_centralizer_coe, hDfix]
    have hQCD : Q ≤ centralizer ((⁅A, Q⁆ : Subgroup G) : Set G) := by
      have hle : MulAut.conj m • zpowers x
          ≤ MulAut.conj m • centralizer ((⁅A, Q⁆ : Subgroup G) : Set G) :=
        pointwise_smul_le_pointwise_smul_iff.mpr hQ₀le
      rwa [hconj, hCfix] at hle
    have hDX : (⁅A, Q⁆ : Subgroup G) ≤ A ⊓ centralizer (Q : Set G) :=
      le_inf hDA (Subgroup.le_centralizer_iff.1 hQCD)
    have hbot : (⁅A, Q⁆ : Subgroup G) = ⊥ := by
      have h := hIDP.inf_eq_bot
      rwa [inf_eq_left.2 hDX] at h
    exact hAQ hbot
  have hQCX : Q ≤ centralizer ((A ⊓ centralizer (Q : Set G) : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.1 inf_le_right
  have hqCX : q ∣ Nat.card ↥(centralizer ((A ⊓ centralizer (Q : Set G) : Subgroup G) : Set G)) := by
    rw [← hQcard]
    exact Subgroup.card_dvd_of_le hQCX
  refine ⟨hDp, hXp, ⟨hIDP.sup_eq, hIDP.inf_eq_bot, hIDP.commutator_eq_bot⟩, hDcent, hMnormD,
    hqCD, hqCX, ?_⟩
  intro g hg
  refine hqCD ?_
  have hcent : centralizer ((A ⊓ centralizer (Q : Set G) : Subgroup G) : Set G)
      = MulAut.conj g⁻¹ • centralizer ((⁅A, Q⁆ : Subgroup G) : Set G) := by
    rw [← hg, CFSG.FeitThompson.Prep08.conjSubgroup,
      ← smul_centralizer_coe]
  rwa [hcent, natCard_conj_smul] at hqCX

end

end CFSG.FeitThompson.Proofs
