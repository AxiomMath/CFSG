module

public import CFSG.FeitThompson.Statements.FittingOverlapKappaStatements
public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.NonTIFittingCyclicComplement
import CFSG.FeitThompson.Local.KappaFreeTauTwoFreeFrobenius
import CFSG.FeitThompson.Local.KappaResidualRankTwoExclusion
import CFSG.FeitThompson.Local.ChiefFactorCentralizationFittingBound
import CFSG.FeitThompson.Local.MixedFittingCentralizerPrimeSupport
import CFSG.FeitThompson.Local.SolvableDerivedKernelCommutators
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import Mathlib

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson Subgroup

universe u

variable {G : Type u} [Group G] [Finite G]

theorem sigmaCore_le_mixedFitting {M : Subgroup G} (hnil : Group.IsNilpotent ↥(sigmaCore M)) :
    sigmaCore M ≤ mixedFitting M := by
  rw [mixedFitting_eq]
  exact le_map_fittingRaw_subtype (sigmaCore_le M) (sigmaCore_normal_subgroupOf M) hnil

omit [Finite G] in
theorem inf_conjSubgroup_ne_bot_of_mem_centralizer {F : Subgroup G} {x y : G}
    (hxF : x ∈ F) (hx1 : x ≠ 1) (hy : y ∈ centralizer ({x} : Set G)) :
    F ⊓ CFSG.FeitThompson.conjSubgroup F y ≠ ⊥ := by
  intro hbot
  have hcomm : x * y = y * x := (mem_centralizer_iff.1 hy) x rfl
  have hxconj : x ∈ CFSG.FeitThompson.conjSubgroup F y := by
    refine CFSG.FeitThompson.mem_conjSubgroup.2 ⟨x, hxF, ?_⟩
    rw [mul_assoc, hcomm]
    group
  exact hx1 (Subgroup.mem_bot.1 (hbot ▸ mem_inf.2 ⟨hxF, hxconj⟩))

theorem ne_bot_of_isInternalSemidirectProduct_sigmaCore {M E : Subgroup G}
    (hsol : Group.IsSolvable ↥M) (hcore : sigmaCore M ≠ ⊥)
    (hle : sigmaCore M ≤ (⁅M, M⁆ : Subgroup G))
    (hsd : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E) : E ≠ ⊥ := by
  intro hE
  have hMeq : M = sigmaCore M := by
    have h := hsd.sup_eq
    rw [hE, sup_bot_eq] at h
    exact h.symm
  have hMle : M ≤ (⁅M, M⁆ : Subgroup G) := hMeq.le.trans hle
  have _inst : Group.IsSolvable ↥M := hsol
  have hbot : M = ⊥ := eq_bot_of_isSolvable_of_le_commutator_self M hMle
  exact hcore (le_bot_iff.1 (hbot ▸ sigmaCore_le M))

theorem kappaResidualSetup_of_residualWitness {M N K U R Nstar : Subgroup G} {r : ℕ}
    (hNc : IsCoatom N) (hMc : IsCoatom M) (hκN : (kappaPrimes N).Nonempty)
    (hrprime : r.Prime) (hrU : r ∣ Nat.card ↥U)
    (hKhall : Prep08.IsHallOf (kappaPrimes N) K N)
    (hUhall : Prep08.IsHallOf {p : ℕ | p.Prime ∧ p ∉ sigmaPrimes N ∧ p ∉ kappaPrimes N} U N)
    (hUbot : U ≠ ⊥) (hUab : IsMulCommutative ↥U)
    (hUfree : ∀ k ∈ K, k ≠ 1 → U ⊓ centralizer ({k} : Set G) = ⊥)
    (hsemiN : FreeCore.IsInternalSemidirectProduct N (sigmaCore N) (M ⊓ N))
    (hsemiMN : FreeCore.IsInternalSemidirectProduct (M ⊓ N) U K)
    (hRsylU : Prep08.IsSylowOf r R U)
    (hNstarC : IsCoatom Nstar)
    (hNstarX : ∃ X : Subgroup G, X ≤ K ∧ (Nat.card ↥X).Prime ∧
      normalizer ((X : Subgroup G) : Set G) ≤ Nstar)
    (hNR : normalizer ((R : Subgroup G) : Set G) ≤ M) :
    Prep08.IsKappaResidualSetup N K U
      (sigmaCore N ⊓ centralizer ((K : Subgroup G) : Set G)) Nstar R M r :=
  have hUK : U ⊔ K = M ⊓ N := hsemiMN.sup_eq
  { isCoatom_M := hNc
    kappa_nonempty := hκN
    isHall_K := hKhall
    isHall_U := hUhall
    semidirect_M := by rw [hUK]; exact hsemiN
    semidirect_UK := by rw [hUK]; exact hsemiMN
    isMulCommutative_U := hUab
    centralizer_U := hUfree
    U_ne_bot := hUbot
    A_eq := rfl
    isCoatom_Mstar := hNstarC
    exists_prime_order_le_K := hNstarX
    prime_r := hrprime
    r_dvd := hrU
    isSylow_R := hRsylU
    isCoatom_H := hMc
    normalizer_R_le := hNR }

theorem FTS_kappa_positive_support_forces_cyclic_frobenius
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_nilpotent_sigma_core_fitting_structure.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_nonnilpotent_sigma_core_hall_structure.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_kappa_local_pair.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_kappa_residual_prime_overgroup_intersection.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_kappa_residual_prime_overgroup_position.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_kappa_residual_rank_two_exclusion.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_nontrivial_kappa_support_residual_witness.{u})
    (h₉ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u}) :
    _root_.CFSG.FeitThompson.Statements.FTS_kappa_positive_support_forces_cyclic_frobenius.{u} := by
  intro G _ _ hG M hM N hN x hxS hx1 hCM hCN hκN
  have hMc : IsCoatom M := hM
  have hNc : IsCoatom N := hN
  have _hfin : Fintype G := Fintype.ofFinite G
  have hamb : IsFTAmbient G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable⟩
  have hG8 : Prep08.IsMinimalSimpleOddOrder G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable⟩
  have hGfbg : IsFBGAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hG2 : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hG3 : Prep03.IsAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  obtain ⟨-, hsemiN, -, r, K, U, R, hrmem, -, -, hRU, -, hKhall, hUbot, hUab,
    hUhall, hsemiMN, hUfree, hRsylU, -, hRcyc, hNR⟩ :=
    h₈ G hG8 M N hMc hNc x hxS hx1 hCM hCN hκN
  have hKhall3 : Prep03.IsHallPiOf (kappaPrimes N) K N := by
    obtain ⟨hKN, hHall⟩ := hKhall
    rw [isHallPiSubgroup_iff] at hHall
    refine ⟨hKN, fun s hs => hHall.1 s ?_, fun s hs => hHall.2 s hs⟩
    rwa [Nat.card_congr (subgroupOfEquivOfLe hKN).toEquiv]
  have hkappaSetup : Prep03.IsKappaSetup G N K (Prep03.cent (sigmaCore N) (K : Set G))
      (K ⊔ Prep03.cent (sigmaCore N) (K : Set G)) :=
    { ambient := hG3
      isCoatom := hNc
      kappa_nonempty := hκN
      isHall_K := hKhall3
      A_eq := rfl
      Z_eq := rfl }
  obtain ⟨Nstar, ⟨hNstarC, hNstarX⟩, -⟩ := h₄ G N K _ _ hkappaSetup
  have hrprime : r.Prime := prime_of_mem_tauTwoPrimes hrmem.1
  have hRbot : R ≠ ⊥ := fun h => hRcyc (by rw [h]; infer_instance)
  have hrU : r ∣ Nat.card ↥U := by
    have _inst : Fact r.Prime := ⟨hrprime⟩
    rcases hRsylU.isPGroup.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.1 h) hRbot
    · exact h.trans (Subgroup.card_dvd_of_le hRU)
  have hsetup := kappaResidualSetup_of_residualWitness hNc hMc hκN hrprime hrU hKhall hUhall
    hUbot hUab hUfree hsemiN hsemiMN hRsylU hNstarC hNstarX hNR
  have hpartner := isKappaResidualPartner_of_isKappaResidualSetup hsetup
  obtain ⟨-, -, -, -, hκM, -⟩ := h₆ G hG8 N K U _ Nstar R M r hsetup
  obtain ⟨hnil, -, -, -⟩ := h₅ G hamb r N K U _ Nstar R M hpartner
  have hτM : tauTwoPrimes M = ∅ := by
    by_contra hne
    obtain ⟨-, -, hτN, -⟩ := h₇ G hG8 N K U _ Nstar R M r hsetup (Set.nonempty_iff_ne_empty.2 hne)
    rw [hτN] at hrmem
    exact absurd hrmem.1 (Set.notMem_empty r)
  obtain ⟨hcore, ⟨E₀, hE₀M, hE₀bot, hsd₀, hfpf₀⟩, hfpf⟩ :=
    FTS_kappa_free_tau_two_free_frobenius h₃ G hamb M hM hκM hτM
  obtain ⟨y, hyC, hyM⟩ : ∃ y ∈ centralizer ({x} : Set G), y ∉ M := by
    by_contra h
    exact hCM fun z hz => by
      by_contra hzM
      exact h ⟨z, hz, hzM⟩
  have hoverlap : mixedFitting M ⊓ conjSubgroup (mixedFitting M) y ≠ ⊥ :=
    inf_conjSubgroup_ne_bot_of_mem_centralizer (sigmaCore_le_mixedFitting hnil hxS) hx1 hyC
  obtain ⟨-, hcycAll⟩ :=
    FBG_nonti_fitting_cyclic_complement h₁ h₂ h₃ h₉ G hGfbg M y hMc hyM hoverlap
  obtain ⟨-, -, hSle⟩ := h₃ G hG2 M hMc
  have hsol : Group.IsSolvable ↥M := hG.isSolvable M hMc.1
  have huniv : ∀ E : Subgroup G, E ≤ M →
      FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E →
      E ≠ ⊥ ∧ IsCyclic ↥E ∧
        ∀ e ∈ E, e ≠ 1 → sigmaCore M ⊓ centralizer ({e} : Set G) = ⊥ := by
    intro E hEM hsd
    obtain ⟨-, hcyc, -⟩ := hcycAll E hEM hsd
    exact ⟨ne_bot_of_isInternalSemidirectProduct_sigmaCore hsol hcore hSle hsd,
      hcyc hτM, hfpf E hEM hsd⟩
  obtain ⟨-, hcyc₀, -⟩ := huniv E₀ hE₀M hsd₀
  exact ⟨hκM, hτM, hnil, ⟨E₀, hE₀M, hcore, hE₀bot, hsd₀, hcyc₀, hfpf₀⟩, huniv⟩

end

end CFSG.FeitThompson.Proofs
