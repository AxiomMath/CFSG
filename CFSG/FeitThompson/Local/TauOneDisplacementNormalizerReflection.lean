module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.TauOneDisplacementReflectedConfiguration
import CFSG.FeitThompson.Local.SigmaPrimeNormalizerFirstPrimeEmbedding
import CFSG.FeitThompson.Local.SigmaComplementPrimeData
import CFSG.FeitThompson.Local.RegularTauAlphaFixedPoints
import CFSG.FeitThompson.Local.AlphaSigmaPrimeSeparation
import CFSG.FeitThompson.Local.SinglePrimeOrbitFixedLine
public import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise CFSG.FeitThompson
  CFSG.FeitThompson

universe u

theorem alphaCoreIn_eq_alphaCoreOf {G : Type*} [Group G] [Finite G] (M : Subgroup G) :
    Prep09.alphaCoreIn M = Prep08.alphaCoreOf M := (rfl)

theorem FTS_tau_one_displacement_normalizer_reflection
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_nonabelian_prime_subgroup_unique_maximum.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_beta_prime_centralizing_sylow.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_plane_maximal_overgroups.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_tau_one_three_prime_normalizer_transfer.{u}) :
    _root_.CFSG.FeitThompson.Statements.FTS_tau_one_displacement_normalizer_reflection.{u} := by
  intro G _ _ hG M hM E hEM hsd p r hp hr hpτ P hPE hPcard R hRCE hRcard q a hq V hVCent hVcard
    hRnormV hQne T hT hNT
  have hsimple := hG.isSimpleGroup
  obtain ⟨hnonconj, hpσT, -, hrτT, hqσM, hqαT, -, hRnormQ, hCQR, -, hfixne⟩ :=
    FTS_tau_one_displacement_reflected_configuration h₁ h₂ h₇ h₈ G hG M hM E hEM hsd p r hp hr
      hpτ P hPE hPcard R hRCE hRcard q a hq V hVCent hVcard hRnormV hQne T hT hNT
  have hVS : V ≤ sigmaCore M := hVCent.trans inf_le_left
  have hVcP : V ≤ centralizer (P : Set G) := hVCent.trans inf_le_right
  have hVT : V ≤ T := (hVcP.trans (centralizer_le_normalizer _)).trans hNT
  have hRE : R ≤ E := hRCE.trans inf_le_left
  have hRcP : R ≤ centralizer (P : Set G) := hRCE.trans inf_le_right
  have hRT : R ≤ T := (hRcP.trans (centralizer_le_normalizer _)).trans hNT
  have hPT : P ≤ T := le_normalizer.trans hNT
  have hQV : (⁅V, R⁆ : Subgroup G) ≤ V := commutator_le_left_of_le_normalizer hRnormV
  have hQM : (⁅V, R⁆ : Subgroup G) ≤ M := (hQV.trans hVS).trans (sigmaCore_le M)
  have hQT : (⁅V, R⁆ : Subgroup G) ≤ T := hQV.trans hVT
  have hQpg : IsPGroup q ↥(⁅V, R⁆ : Subgroup G) := (IsPGroup.of_card hVcard).to_le hQV
  have hTM : T ≠ M := fun h => hnonconj 1 (by rw [Prep09.conjSub_one]; exact h)
  have hnc : ∀ g : G, MulAut.conj g • M ≠ T := by
    intro g hg
    refine hnonconj g⁻¹ ?_
    rw [← hg, Prep09.conjSub_def, inv_inv]
    exact Subgroup.toSubmonoid_inj.mp rfl
  obtain ⟨hHallMof, -, -⟩ :=
    haveI : Fintype G := Fintype.ofFinite G
    h₁ G ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩ M hM
  have hrσM : r ∉ sigmaPrimes M := by
    have h := hHallMof.2.notMem_of_mem_primeFactors_index
    rw [index_subgroupOf_left_eq hsd] at h
    exact h r (Nat.mem_primeFactors.2
      ⟨hr, hRcard ▸ Subgroup.card_dvd_of_le hRE, Nat.card_pos.ne'⟩)
  have hrq : r ≠ q := fun h => hrσM (h ▸ hqσM)
  have hATne : Prep08.alphaCoreOf T ≠ ⊥ := by
    intro hb
    refine hfixne ?_
    rw [Prep09.centIn_def, alphaCoreIn_eq_alphaCoreOf, hb, bot_inf_eq]
  have hG08 : Prep08.IsMinimalSimpleOddOrder G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
  have huniq : IsUniqueMaximalOvergroup (normalizer ((⁅V, R⁆ : Subgroup G) : Set G)) T := by
    refine (isUniqueMaximalOvergroup_iff _ _).2 ?_
    by_contra hne
    have hsetup : Prep08.IsRegularTauOneAlphaSetup T R (⁅V, R⁆ : Subgroup G) r q :=
      { isCoatom_M := hT
        mem_tau1 := hrτT
        prime_q := hq
        q_ne := fun h => hrq h.symm
        q_notMem_alpha := hqαT
        le_P := hRT
        natCard_P := hRcard
        le_Q := hQT
        Q_ne_bot := hQne
        isPGroup_Q := hQpg
        normalized := hRnormQ
        centralizer_eq := hCQR
        not_unique := hne }
    obtain ⟨-, hfix⟩ :=
      FTS_regular_tau_one_alpha_fixed_points G hG08 T R (⁅V, R⁆ : Subgroup G) r q hsetup hATne
    refine hfixne ?_
    rw [Prep09.centIn_def, alphaCoreIn_eq_alphaCoreOf, sup_comm]
    exact hfix
  obtain ⟨hqσT, hAM, -, -, hτsub⟩ :=
    haveI : Fintype G := Fintype.ofFinite G
    FBG_sigma_prime_normalizer_first_prime_embedding h₁ h₃ h₄ h₅ h₆ h₇ G
      ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
      M T hM hT (Ne.symm hTM) q hq hqσM (⁅V, R⁆ : Subgroup G) hQM hQne hQpg huniq.le p hp hpτ
      hpσT P (le_inf (hPE.trans hEM) hPT) hPcard
  have hqαM : q ∉ alphaPrimes ↥M := fun hmem =>
    notMem_sigmaPrimes_of_mem_alphaPrimes_of_not_conj hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable_of_ne_top hM hT hnc hmem hqσT
  have hrαM : r ∉ alphaPrimes ↥M := fun hmem =>
    hrσM (alphaPrimes_subset_sigmaPrimes hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable_of_ne_top hM hmem)
  have hrτM : r ∈ tau1Primes M := (hτsub hrτT).resolve_right hrαM
  exact ⟨huniq, hqσT, hqαM, hrτM, hAM⟩

end

end CFSG.FeitThompson.Proofs
