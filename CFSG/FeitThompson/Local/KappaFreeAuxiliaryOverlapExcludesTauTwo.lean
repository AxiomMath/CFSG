module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.AuxiliaryOppositeTauTwoRankOne
import CFSG.FeitThompson.Local.RegularPlaneFixedLinesNotConjugate
import CFSG.FeitThompson.Local.SigmaComplementPlaneActionSupport
import CFSG.FeitThompson.Local.SigmaComplementThreeHallFactors
import CFSG.FeitThompson.Local.NonabelianAmbientSingleRankTwoPrime
import CFSG.FeitThompson.Local.SigmaPrimeNormalizerOutsideComplement
import CFSG.FeitThompson.Local.SigmaPrimeNormalizerNarrowRankBound
import CFSG.FeitThompson.Local.KappaHallThirdFactorSupportedComplement
import CFSG.FeitThompson.Local.KappaPrimeLineFixedEquivalence
import CFSG.FeitThompson.Local.NonuniqueScnAuxiliaryPrime
import CFSG.FeitThompson.Local.MaximalPlaneDerivedNormalComplement
import CFSG.FeitThompson.Local.InvariantRankTwoFactorsFixedFreeCycle
import CFSG.FeitThompson.Local.BetaPrimesSigmaCompatibility
import CFSG.FeitThompson.Local.ThreePrimeComplementDecomposition
import CFSG.FeitThompson.Local.SmallRankLineInMaximalPlane
import CFSG.FeitThompson.Local.MixedFittingCentralizerPrimeSupport
import CFSG.FeitThompson.OddOrder.FittingSplitsOverHallCore
import CFSG.FeitThompson.OddOrder.PConfigCoprimeFrobeniusAction
import CFSG.FeitThompson.OddOrder.SigmaCentralizerTransitivity
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

open CFSG.FeitThompson CFSG.FeitThompson Subgroup
  Pointwise

universe u

theorem FTS_kappa_free_auxiliary_overlap_excludes_tau_two
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_tau_two_full_central_hall.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FBG_tau_two_hall_abelian.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_nonabelian_ambient_unique_nonregular_line.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_beta_or_derived_line_centralizer_unique.{u})
    (h₉ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u}) :
    _root_.CFSG.FeitThompson.Statements.FTS_kappa_free_auxiliary_overlap_excludes_tau_two.{u} := by
  intro G _ _ hG M hM T hT hτ hβ hκ hσ hx hoverlap
  have hMc : IsCoatom M := hM
  have hTc : IsCoatom T := hT
  have hsimple : IsSimpleGroup G := hG.isSimpleGroup
  let _ : Fintype G := Fintype.ofFinite G
  have hG2 : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hG4 : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hG6 : Prep06.IsMinimalOddSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hG8 : Prep08.IsMinimalSimpleOddOrder G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable⟩
  obtain ⟨x, hxS, hx1, hxT⟩ := hx
  obtain ⟨q, hqM, hqσT⟩ := hoverlap
  have hqp : q.Prime := (mem_sigmaPrimes_iff.1 hqσT).1
  have hqβT : q ∈ betaPrimes ↥T := hβ q hqM hqσT
  have hqσM : q ∉ sigmaPrimes M := fun h => by
    have hmem : q ∈ sigmaPrimes M ∩ sigmaPrimes T := ⟨h, hqσT⟩
    rw [hσ] at hmem; exact hmem
  have hqodd : Odd q :=
    hG.odd_natCard.of_dvd_nat (hqM.trans (Subgroup.card_subgroup_dvd_card M))
  obtain ⟨z, hzM, hzo⟩ := exists_mem_orderOf_eq_of_dvd hqp hqM
  set Q : Subgroup G := zpowers z with hQdef
  have hQM : Q ≤ M := zpowers_le.2 hzM
  have hQcard : Nat.card ↥Q = q := by rw [hQdef, Nat.card_zpowers, hzo]
  have hQpg : IsPGroup q ↥Q := IsPGroup.of_card (by rw [pow_one, hQcard])
  obtain ⟨g, hQST⟩ := exists_conj_le_sigmaCore hqp (h₁ G hG2 T hTc).2.1 hqσT hQpg
  set T' : Subgroup G := MulAut.conj g • T with hT'def
  have hT'c : IsCoatom T' := isCoatom_conj_smul hTc g
  have hQT' : Q ≤ T' := hQST.trans (sigmaCore_le T')
  have hqβT' : q ∈ betaPrimes ↥T' := by rw [hT'def, betaPrimes_conj_smul]; exact hqβT
  have hCQ : centralizer (Q : Set G) ≤ T' :=
    (h₈ G hG6 T' Q hT'c q hqp hQT' hQcard (Or.inl hqβT')).1.le
  have hQπ : IsPiSubgroup ((sigmaPrimes M)ᶜ) Q := by
    refine isPiSubgroup_iff.2 fun s hs => ?_
    obtain ⟨hsp, hsd, -⟩ := Nat.mem_primeFactors.1 hs
    rw [hQcard] at hsd
    rw [(Nat.prime_dvd_prime_iff_eq hsp hqp).1 hsd]
    exact hqσM
  obtain ⟨E, hQE, hsd⟩ :=
    exists_isInternalSemidirectProduct_sigmaCore_ge hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable hMc hQM hQπ
  have hEM : E ≤ M := hsd.right_le
  rw [Set.eq_empty_iff_forall_notMem]
  intro p hp
  have hpp : p.Prime := prime_of_mem_tauTwoPrimes hp
  have hpσM : p ∉ sigmaPrimes M := notMem_sigmaPrimes_of_mem_tauTwoPrimes hp
  have hpodd : Odd p :=
    hG.odd_natCard.of_dvd_nat
      ((dvd_natCard_of_mem_tauTwoPrimes hp).trans (Subgroup.card_subgroup_dvd_card M))
  have hrankT : elementaryAbelianPRank p ↥T ≤ 1 :=
    FTS_auxiliary_opposite_tau_two_rank_one h₆ G hG6 M T hMc hTc hτ
      (fun r _ hrM hrT => hβ r hrM hrT) p hp
  obtain ⟨A, hAE, hAplane⟩ := exists_plane_le_of_isInternalSemidirectProduct hp hsd
  have hAM : A ≤ M := hAE.trans hEM
  have hAcard : Nat.card ↥A = p ^ 2 := hAplane.natCard'
  have hAea : IsElementaryAbelian p A :=
    isElementaryAbelian_iff_isElementaryAbelianSubgroup.2 hAplane.isElementaryAbelianSubgroup
  have hAQ : (⁅A, Q⁆ : Subgroup G) ≠ ⊥ := by
    intro hbot
    have hAC : A ≤ centralizer (Q : Set G) := commutator_eq_bot_iff_le_centralizer.1 hbot
    have hle := hAea.le_elementaryAbelianPRank hpp hAcard (hAC.trans hCQ)
    rw [hT'def, elementaryAbelianPRank_conj_smul hpp.one_lt] at hle
    omega
  have hosA : _root_.CFSG.FeitThompson.IsOutsideSigmaPlane p M A := ⟨hMc, hpp, hpσM, hAM, hAplane⟩
  have hscA : _root_.CFSG.FeitThompson.IsSigmaComplement M E := ⟨hMc, hsd⟩
  have hEnormA : E ≤ normalizer (A : Set G) := (h₅ G hG4 p M A E hosA hscA hAE).1
  have hQnc : ¬ Q ≤ centralizer (A : Set G) := by
    intro hle
    have h0 : (⁅Q, A⁆ : Subgroup G) = ⊥ := commutator_eq_bot_iff_le_centralizer.2 hle
    rw [← Subgroup.commutator_comm] at h0
    exact hAQ h0
  have hQinf : Q ⊓ centralizer (A : Set G) = ⊥ := by
    have hdvd : Nat.card ↥(Q ⊓ centralizer (A : Set G)) ∣ q := by
      rw [← hQcard]; exact Subgroup.card_dvd_of_le inf_le_left
    rcases hqp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
    · exact Subgroup.card_eq_one.1 h1
    · exact absurd (le_trans (Subgroup.eq_of_le_of_card_ge inf_le_left
        (by rw [hQcard, h1])).ge inf_le_right) hQnc
  have hqdvd : q ∣ (E ⊓ centralizer (A : Set G)).relIndex E := by
    have hCnormal : ((centralizer (A : Set G)).subgroupOf E).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer (hEnormA.trans (normalizer_le_normalizer_centralizer A))
    have hdisj : Disjoint ((centralizer (A : Set G)).subgroupOf E) (Q.subgroupOf E) := by
      rw [Subgroup.disjoint_def]
      intro y hy1 hy2
      have hy : (y : G) ∈ Q ⊓ centralizer (A : Set G) := Subgroup.mem_inf.2 ⟨hy2, hy1⟩
      rw [hQinf] at hy
      exact Subtype.ext (by simpa using hy)
    have h := natCard_dvd_index_of_disjoint _ _ hdisj
    rw [natCard_subgroupOf hQE, hQcard] at h
    rwa [Subgroup.relIndex, Subgroup.inf_subgroupOf_left]
  obtain ⟨E₁, E₂, E₃, hsplit, -⟩ := FNI_sigma_complement_three_factors h₁ G hG4 M E hscA
  have hsupp := FBG_sigma_complement_plane_action_support h₃ h₅ h₆ G hG2 M hMc p hpp hpσM A hAM
    hAplane E hsd hAE E₁ E₂ E₃ ⟨hsplit.le_E₁, hsplit.isHall_E₁⟩ ⟨hsplit.le_E₂, hsplit.isHall_E₂⟩
    ⟨hsplit.le_E₃, hsplit.isHall_E₃⟩ hsplit.outer hsplit.inner
  have hrelne : (E ⊓ centralizer (A : Set G)).relIndex E ≠ 0 := by
    rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite
  have hqτ₁ : q ∈ tau1Primes M := hsupp.2.2 q (Nat.mem_primeFactors.2 ⟨hqp, hqdvd, hrelne⟩)
  have hcycM : ∃ S : Sylow q ↥M, IsCyclic ((S : Subgroup ↥M).map M.subtype : Subgroup G) :=
    exists_isCyclic_sylow_of_elementaryAbelianPRank_le_one M hqp hqodd
      (le_of_eq (elementaryAbelianPRank_eq_one_of_mem_tau1Primes hqτ₁))
  have hSQ : sigmaCore M ⊓ centralizer (Q : Set G) = ⊥ := by
    by_contra hne
    have hmem := (mem_kappaPrimes_iff_inf_centralizer_ne_bot hqp hqσM hcycM hQM hQcard).2 hne
    rw [hκ] at hmem
    exact hmem
  obtain ⟨hDcard, hXcard, -, hDcent, -, -, -, hnotconj⟩ :=
    FTS_regular_plane_fixed_lines_not_conjugate h₁ h₂ h₄ h₅ h₆ h₇ h₉ G hG8 M E A Q
      (⁅A, Q⁆ : Subgroup G) (A ⊓ centralizer (Q : Set G)) p q hMc hEM hsd hp hAE
      ⟨hAea, hAcard⟩ hqτ₁ hQE hQcard hSQ hAQ rfl rfl
  have hDT : (⁅A, Q⁆ : Subgroup G) ≤ T :=
    le_trans (le_trans (hDcent.le.trans inf_le_right)
      (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hxS))) hxT
  have hXT' : (A ⊓ centralizer (Q : Set G)) ≤ T' := le_trans inf_le_right hCQ
  have hXT : (MulAut.conj g⁻¹ • (A ⊓ centralizer (Q : Set G)) : Subgroup G) ≤ T := by
    have h := (pointwise_smul_le_pointwise_smul_iff (a := MulAut.conj g⁻¹)).2 hXT'
    rwa [hT'def, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at h
  have hXgcard : Nat.card ↥(MulAut.conj g⁻¹ • (A ⊓ centralizer (Q : Set G)) : Subgroup G) = p := by
    rw [natCard_conj_smul, hXcard]
  obtain ⟨m, hmT, hconj⟩ :=
    exists_mem_conj_smul_eq_of_natCard_eq_of_elementaryAbelianPRank_le_one hpp hpodd hrankT
      hDT hXT hDcard hXgcard
  refine hnotconj (g * m)⁻¹ ?_
  rw [Prep08.conjSubgroup, inv_inv, map_mul, mul_smul, hconj, ← mul_smul, ← map_mul,
    mul_inv_cancel, map_one, one_smul]

end

end CFSG.FeitThompson.Proofs
