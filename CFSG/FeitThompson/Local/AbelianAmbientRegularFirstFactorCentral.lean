module

public import CFSG.FeitThompson.Statements.FittingOverlapKappaStatements
public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.AbelianAmbientCharacteristicChain
import CFSG.FeitThompson.Local.AbelianAmbientNormalizerChain
import CFSG.FeitThompson.Local.OutsideSigmaFixedFreeLineCommutator
import CFSG.FeitThompson.Local.AbelianActionNormalFixedDisplacement
import CFSG.FeitThompson.Local.MinimalPrimeCentralizerCounterexample
import CFSG.FeitThompson.Local.InvariantRankTwoFactorsFixedFreeCycle
import CFSG.FeitThompson.Local.MixedFittingComplementCoreEquality
import CFSG.FeitThompson.Local.SinglePrimeOrbitFixedLine
import CFSG.FeitThompson.Local.ThreePrimeComplementDecomposition
import CFSG.FeitThompson.Local.FittingSplitsNormalHall
import CFSG.FeitThompson.Local.MixedFittingCentralizerPrimeSupport
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

open CFSG.FeitThompson Subgroup

universe u

variable {G : Type u} [Group G]

theorem commutator_coe_le_centralizer_subgroupOf {N K : Subgroup G}
    (h : ⁅N, N⁆ ≤ centralizer (K : Set G)) :
    _root_.commutator ↥N ≤ centralizer ((K.subgroupOf N : Subgroup ↥N) : Set ↥N) := by
  intro x hx
  have hxG : (x : G) ∈ (⁅N, N⁆ : Subgroup G) := by
    rw [← Subgroup.map_subtype_commutator]
    exact ⟨x, hx, rfl⟩
  have hxc := h hxG
  rw [mem_centralizer_iff]
  intro y hy
  exact Subtype.ext (mem_centralizer_iff.1 hxc y (mem_subgroupOf.1 hy))

theorem FBG_abelian_ambient_regular_first_factor_central
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_tau_two_full_central_hall.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u}) :
    _root_.CFSG.FeitThompson.Statements.FBG_abelian_ambient_regular_first_factor_central.{u} := by
  intro G _ _ hG M p A E P E₁ E₂ E₃ K hsetup hdec q hq X hXE₁ hXq hSX
  have := hG.isSimpleGroup
  have hGosm : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hG8 : CFSG.FeitThompson.Prep08.IsMinimalSimpleOddOrder G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable⟩
  obtain ⟨hMc, hp, hpσ, hAM, hplane, hEM, hsd, hAE, -, -, -⟩ := id hsetup
  have hosp : _root_.CFSG.FeitThompson.IsOutsideSigmaPlane p M A := ⟨hMc, hp, hpσ, hAM, hplane⟩
  obtain ⟨hcyc₁, -, hKab, hnK, -, -, -, -, -, -, -, -, -⟩ :=
    FBG_abelian_ambient_characteristic_chain h₁ h₂ h₃ h₄ h₅ G hG M p A E P E₁ E₂ E₃ K hsetup hdec
  obtain ⟨-, -, -, -, hEN, hKNnormal, hN'⟩ :=
    FBG_abelian_ambient_normalizer_chain h₁ h₂ h₃ h₄ h₅ G hG M p A E P E₁ E₂ E₃ K hsetup hdec
  set N : Subgroup G := normalizer (A : Set G) with hNdef
  have hKE : K ≤ E := by
    rw [hdec.K_eq]; exact sup_le hdec.le_E_E₂ hdec.le_E_E₃
  have hEnormK : E ≤ normalizer ((K : Subgroup G) : Set G) :=
    le_normalizer_of_normal_subgroupOf hKE hnK
  have hXE : X ≤ E := hXE₁.trans hdec.le_E_E₁
  have hXM : X ≤ M := hXE.trans hEM
  have hXnormK : X ≤ normalizer ((K : Subgroup G) : Set G) := hXE.trans hEnormK
  have hqτ₁ : q ∈ tau1Primes M := by
    have hpi := hdec.hall_E₁.isPiSubgroup
    rw [isPiSubgroup_iff] at hpi
    refine hpi q (Nat.mem_primeFactors.2 ⟨hq, ?_, Nat.card_pos.ne'⟩)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hdec.le_E_E₁).toEquiv]
    exact hXq ▸ Subgroup.card_dvd_of_le hXE₁
  have hqσ : q ∉ sigmaPrimes M := notMem_sigmaPrimes_of_mem_tau1Primes hqτ₁
  have hn₃ : (E₃.subgroupOf E).Normal := hdec.semidirect_outer.normal_subgroupOf
  have hKhall : IsHallSubgroup (tauTwoPrimes M ∪ tau3Primes M) (K.subgroupOf E) := by
    have hKsub : K.subgroupOf E = E₂.subgroupOf E ⊔ E₃.subgroupOf E := by
      rw [hdec.K_eq, Subgroup.subgroupOf_sup hdec.le_E_E₂ hdec.le_E_E₃]
    rw [hKsub]
    exact (isHallSubgroup_iff_isHallPiSubgroup.2 hdec.hall_E₂).sup
      (isHallSubgroup_iff_isHallPiSubgroup.2 hdec.hall_E₃)
      (fun s hs => notMem_tau3Primes_of_mem_tauTwoPrimes hs)
  have hKprimes : ∀ s : ℕ, s.Prime → s ∣ Nat.card ↥K → s ∈ tauTwoPrimes M ∪ tau3Primes M := by
    intro s hs hdvd
    refine isPiNumber_iff.1 hKhall.natCard s (Nat.mem_primeFactors.2 ⟨hs, ?_, Nat.card_pos.ne'⟩)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKE).toEquiv]
  have hKσ : ∀ s : ℕ, s.Prime → s ∣ Nat.card ↥K → s ∉ sigmaPrimes M := by
    intro s hs hdvd
    rcases hKprimes s hs hdvd with h | h
    · exact notMem_sigmaPrimes_of_mem_tauTwoPrimes h
    · exact notMem_sigmaPrimes_of_mem_tau3Primes h
  have hqK : ¬ q ∣ Nat.card ↥K := by
    intro hdvd
    rcases hKprimes q hq hdvd with h | h
    · have h2 := elementaryAbelianPRank_eq_two_of_mem_tauTwoPrimes h
      have h1 := elementaryAbelianPRank_eq_one_of_mem_tau1Primes hqτ₁
      omega
    · exact Set.disjoint_left.1 (disjoint_tau1Primes_tau3Primes M) hqτ₁ h
  obtain ⟨-, -, hMD⟩ :=
    FTS_outside_sigma_fixed_free_line_commutator h₁ h₅ h₆ G hG8 M K X q hMc hq hqσ
      (hKE.trans hEM) hKab hKσ hqK (le_inf hXnormK hXM) hXq hSX
  set D : Subgroup G := ⁅K, X⁆ with hDdef
  have hDK : D ≤ K := commutator_le_left_of_le_normalizer hXnormK
  have hDM : D ≤ M := (hDK.trans hKE).trans hEM
  have hKN : K ≤ N := hKE.trans hEN
  have hXN : X ≤ N := hXE.trans hEN
  have hDN : D ≤ N := hDK.trans hKN
  have hDnormalN : (D.subgroupOf N).Normal := by
    have hc := commutator_coe_le_centralizer_subgroupOf (N := N) (K := K) hN'
    have := hKNnormal
    have hres := normal_commutator_of_commutator_le_centralizer (D := K.subgroupOf N) hc
      (X.subgroupOf N)
    rwa [commutator_subgroupOf hKN hXN] at hres
  have hNnormD : N ≤ normalizer ((D : Subgroup G) : Set G) :=
    le_normalizer_of_normal_subgroupOf hDN hDnormalN
  have hNM : ¬ N ≤ M := (h₃ G hGosm p M A E hosp ⟨hMc, hsd⟩ hAE).2.2.2.2
  have hDbot : D = ⊥ := by
    by_contra hDne
    exact hNM (hNnormD.trans (le_of_eq (normalizer_eq_of_isCoatom hMc hDne hDM hMD)))
  have hKX : K ≤ centralizer ((X : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hDbot
  have hE₁X : E₁ ≤ centralizer ((X : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.1
      (hXE₁.trans (Subgroup.le_centralizer_iff_isMulCommutative.2 hcyc₁.isMulCommutative))
  have hEeq : E = K ⊔ E₁ := by
    have h1 := hdec.semidirect_outer.sup_eq
    rw [hdec.K_eq, ← h1, sup_comm E₂ E₃]
    exact (by ac_rfl : E₃ ⊔ (E₂ ⊔ E₁) = E₃ ⊔ E₂ ⊔ E₁).symm ▸ rfl
  rw [centreIn_eq]
  refine le_inf hXE ?_
  rw [hEeq, ← Subgroup.le_centralizer_iff]
  exact sup_le hKX hE₁X

end

end CFSG.FeitThompson.Proofs
