module

public import CFSG.FeitThompson.Statements.FittingOverlapKappaStatements
public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.KappaNontrivialComplementStructure
import CFSG.FeitThompson.Local.KappaResidualInPrescribedComplement
import CFSG.FeitThompson.Local.NoncyclicSigmaNormalizer
import CFSG.FeitThompson.Local.MaximalTauTwoNonemptyTypeIOrII
import CFSG.FeitThompson.Local.NonuniqueLinesAlphaCoreTrivial
import CFSG.FeitThompson.Representations.TypeISupportingGroupConfiguration
import CFSG.FeitThompson.Local.CommonSylowNormalizerBetaFactor
import CFSG.FeitThompson.Local.SigmaCoreConjugation
import CFSG.FeitThompson.Local.PowerCentralizerTiCriterion
import CFSG.FeitThompson.OddOrder.MaximalSubgroupsSelfNormalizing
import Mathlib.Tactic.Group

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson
open CFSG.FeitThompson.Prep08

universe u

variable {G : Type*} [Group G] {π : Set ℕ} {r : ℕ}

theorem one_lt_sigmaMultiplicity_of_centralizer_not_le [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) {M : Subgroup G} (hM : IsCoatom M) {x : G}
    (hxS : x ∈ sigmaCore M) (hnle : ¬ centralizer ({x} : Set G) ≤ M) :
    1 < sigmaMultiplicity x := by
  obtain ⟨y, hy, hyM⟩ := SetLike.not_le_iff_exists.1 hnle
  have hcomm : x * y = y * x := (Subgroup.mem_centralizer_iff.1 hy) x rfl
  have hfix : y⁻¹ * x * y = x := by
    calc y⁻¹ * x * y = y⁻¹ * (x * y) := by group
      _ = y⁻¹ * (y * x) := by rw [hcomm]
      _ = x := by group
  have hco : IsCoatom (M.map (MulAut.conj y : G →* G)) := isCoatom_map_conj hM y
  have hsig : x ∈ sigmaCore (M.map (MulAut.conj y : G →* G)) := by
    rw [mem_sigmaCore_map_conj_iff, hfix]; exact hxS
  have hne : M ≠ M.map (MulAut.conj y : G →* G) := by
    intro h
    refine hyM ?_
    have hnorm : normalizer (M : Set G) = M := normalizer_coe_eq_of_isCoatom hna hM
    rw [← hnorm]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2 h.symm
  rw [sigmaMultiplicity_eq_ncard]
  exact Set.one_lt_ncard_iff_nontrivial_and_finite.2
    ⟨⟨M, mem_sigmaSupportingMaximals.2 ⟨hM, hxS⟩, M.map (MulAut.conj y : G →* G),
      mem_sigmaSupportingMaximals.2 ⟨hco, hsig⟩, hne⟩, Set.toFinite _⟩

theorem exists_isSylowOf_of_isHallPiSubgroupOf [Finite G] {U N : Subgroup G}
    (hr : r.Prime) (hU : IsHallPiSubgroupOf π U N) (hrπ : r ∈ π) :
    ∃ R : Subgroup G, R ≤ U ∧ IsSylowOf r R U ∧ IsSylowOf r R N := by
  have := Fact.mk hr
  refine ⟨((default : Sylow r ↥U) : Subgroup ↥U).map U.subtype, Subgroup.map_subtype_le _,
    ⟨default, rfl⟩, ?_⟩
  rw [isSylowOf_iff_natCard hr ((Subgroup.map_subtype_le _).trans hU.le),
    Subgroup.card_subtype, (default : Sylow r ↥U).card_eq_multiplicity,
    ← factorization_natCard_eq_of_isHallPiSubgroup_subgroupOf hr hU.1 hU.2 hrπ]

theorem FTS_nontrivial_kappa_support_residual_witness
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₃ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₄ : Statements.FTS_outside_sigma_plane_structure.{u})
    (h₅ : Statements.FTS_plane_maximal_overgroups.{u})
    (h₆ : Statements.FTS_proper_subgroup_p_length_one.{u})
    (h₇ : Statements.FTS_signalizer_unique_supporting_maximum.{u}) :
    Statements.FTS_nontrivial_kappa_support_residual_witness.{u} := by
  intro G _ _ hG M N hM hN x hxS hx1 hnle hCN hκ
  have hsimple : IsSimpleGroup G := hG.isSimpleGroup
  have hG01 : IsFBGAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG07 : IsFTAmbient G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
  have hG09 : Prep09.IsMinimalSimpleOddOrder G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hk : 1 < sigmaMultiplicity x :=
    one_lt_sigmaMultiplicity_of_centralizer_not_le hG.not_isMulCommutative hM hxS hnle
  have hxU : x ∈ sigmaSupport G := mem_sigmaSupport.2 ⟨M, hM, hxS, hx1⟩
  have hMx : M ∈ sigmaSupportingMaximals (G := G) x := mem_sigmaSupportingMaximals.2 ⟨hM, hxS⟩
  obtain ⟨⟨T, -, hTuniq⟩, hclauses⟩ := h₇ G hG09 x hxU hk
  have huniq : IsUniqueMaximalOvergroup (centralizer ({x} : Set G)) N := by
    refine ⟨hN, hCN, fun {Y} hY hYle => ?_⟩
    rw [hTuniq Y ⟨hY, hYle⟩, hTuniq N ⟨hN, hCN⟩]
  obtain ⟨-, -, hprimes, hMall⟩ := hclauses N hN hCN
  obtain ⟨-, -, hsd, -, hτσ, -⟩ := hMall M hMx
  have hord0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
  have hord1 : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.1 h)
  obtain ⟨r, hrmem⟩ := Nat.nonempty_primeFactors.2 (show 1 < orderOf x by omega)
  have hrp : r.Prime := Nat.prime_of_mem_primeFactors hrmem
  have hrτ : r ∈ tauTwoPrimes N := hprimes r hrp (Nat.dvd_of_mem_primeFactors hrmem)
  have hrσM : r ∈ sigmaPrimes M := hτσ hrτ
  obtain ⟨K, U, hKE, hUE, hKhall, hUab, hUhall, hEUK, hNUK, hfree⟩ :=
    FTS_kappa_residual_in_prescribed_complement h₂ G hG07 N hN hκ (M ⊓ N) inf_le_right hsd
  have hrπ : r ∈ {s : ℕ | s.Prime ∧ s ∉ sigmaPrimes N ∧ s ∉ kappaPrimes N} :=
    ⟨hrp, notMem_sigmaPrimes_of_mem_tauTwoPrimes hrτ, notMem_kappaPrimes_of_mem_tauTwoPrimes hrτ⟩
  obtain ⟨R, hRU, hRsylU, hRsylN⟩ := exists_isSylowOf_of_isHallPiSubgroupOf hrp hUhall hrπ
  have hRnc : ¬ IsCyclic ↥R := by
    refine not_isCyclic_of_elementaryAbelianPRank_eq_two hrp ?_
    rw [elementaryAbelianPRank_of_isSylowOf hrp hRsylN,
      elementaryAbelianPRank_eq_two_of_mem_tauTwoPrimes hrτ]
  have hRne : R ≠ ⊥ := fun h => hRnc (h ▸ inferInstanceAs (IsCyclic (⊥ : Subgroup G)))
  have hUne : U ≠ ⊥ := fun h => hRne (le_bot_iff.1 (h ▸ hRU))
  have hUKsplit : FreeCore.IsInternalSemidirectProduct (U ⊔ K) U K := by
    rw [hEUK.sup_eq]; exact hEUK
  have hKprime : (Nat.card ↥K).Prime :=
    (FBG_kappa_nontrivial_complement_structure h₁ h₂ h₃ h₄ h₆ G hG01 N K U
      ⟨hN, hκ, hKhall.1, hKhall.2, hUhall.1, hUne, hNUK, hUKsplit⟩).1
  have hRM : R ≤ M := (hRU.trans hUE).trans inf_le_left
  have hNormR : normalizer ((R : Subgroup G) : Set G) ≤ M :=
    FTS_noncyclic_sigma_normalizer h₅ G hG M R r hM hrσM hRM hRsylN.isPGroup hRnc
  exact ⟨huniq, hsd, ⟨r, hrτ⟩, r, K, U, R, ⟨hrτ, hrσM⟩, hKE, hUE, hRU, hKprime,
    ⟨hKhall.1, hKhall.2⟩, hUne, hUab, ⟨hUhall.1, hUhall.2⟩, hEUK, hfree, hRsylU, hRsylN, hRnc,
    hNormR⟩

end

end CFSG.FeitThompson.Proofs
