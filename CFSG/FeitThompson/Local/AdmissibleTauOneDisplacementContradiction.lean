module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.TauOneDisplacementNormalizerReflection
import CFSG.FeitThompson.Local.TauOneDisplacementReflectedConfiguration
import CFSG.FeitThompson.Local.RegularTauAlphaFixedPoints
import CFSG.FeitThompson.Local.SinglePrimeOrbitFixedLine
import CFSG.FeitThompson.Local.ControlledPlaneCentralizersPrimeCore
import CFSG.FeitThompson.Local.PComplementControlSylowNormalizer
public import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson CFSG.FeitThompson

universe u

variable {G : Type*} [Group G]

theorem commutator_le_centralizer_of_le_normalizer_of_le_centralizer {D V R : Subgroup G}
    (hV : V ≤ normalizer (D : Set G)) (hR : R ≤ centralizer (D : Set G)) :
    (⁅V, R⁆ : Subgroup G) ≤ centralizer (D : Set G) := by
  rw [Subgroup.commutator_le]
  intro v hv y hy
  rw [commutatorElement_def]
  refine mem_centralizer_iff.2 fun d hd => ?_
  have hcent : ∀ x ∈ D, x * y = y * x := fun x hx => mem_centralizer_iff.1 (hR hy) x hx
  have hd' : v⁻¹ * d * v ∈ D := by
    refine (mem_normalizer_iff.1 (hV hv) (v⁻¹ * d * v)).2 ?_
    have he : v * (v⁻¹ * d * v) * v⁻¹ = d := by group
    rw [he]; exact hd
  have e1 : y⁻¹ * d * y = d := by
    rw [mul_assoc, hcent d hd, ← mul_assoc, inv_mul_cancel, one_mul]
  have e2 : y * (v⁻¹ * d * v) * y⁻¹ = v⁻¹ * d * v := by
    rw [← hcent _ hd', mul_inv_cancel_right]
  have key : (v * y * v⁻¹ * y⁻¹) * d * (v * y * v⁻¹ * y⁻¹)⁻¹ = d := by
    calc (v * y * v⁻¹ * y⁻¹) * d * (v * y * v⁻¹ * y⁻¹)⁻¹
        = v * y * v⁻¹ * (y⁻¹ * d * y) * v * y⁻¹ * v⁻¹ := by group
      _ = v * (y * (v⁻¹ * d * v) * y⁻¹) * v⁻¹ := by rw [e1]; group
      _ = v * (v⁻¹ * d * v) * v⁻¹ := by rw [e2]
      _ = d := by group
  exact (mul_inv_eq_iff_eq_mul.1 key).symm

theorem alphaCoreIn_prep06_eq_alphaCoreOf [Finite G] (M : Subgroup G) :
    Prep06.alphaCoreIn M = Prep08.alphaCoreOf M := (rfl)

theorem FTS_admissible_tau_one_displacement_contradiction
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_nonabelian_prime_subgroup_unique_maximum.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_beta_prime_centralizing_sylow.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_plane_maximal_overgroups.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_tau_one_three_prime_normalizer_transfer.{u}) :
    _root_.CFSG.FeitThompson.Statements.FTS_admissible_tau_one_displacement_contradiction.{u} := by
  intro G _ _ hG M E hM hEM hsup hinf p r q a hp hr hq hpτ P R V T hPE hPcard hRCE hRcard
    hVCent hVcard hRnormV hQne hT hNT hadm hdisj
  have := hG.simple
  have hGmin : Prep09.IsMinimalSimpleOddOrder G := ⟨hG.odd, hG.simple, hG.nonabelian, hG.solvable⟩
  have hsd : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E :=
    ⟨hsup, le_normalizer_sigmaCore M, disjoint_iff.2 hinf⟩
  obtain ⟨huniq, -, hqαM, hrτM, hAMne⟩ :=
    FTS_tau_one_displacement_normalizer_reflection h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ G hGmin M hM E hEM hsd
      p r hp hr hpτ P hPE hPcard R hRCE hRcard q a hq V hVCent hVcard hRnormV hQne T hT hNT
  obtain ⟨hnonconj, -, -, -, hqσM, -, -, hRnormQ, hCQR, -, -⟩ :=
    FTS_tau_one_displacement_reflected_configuration h₁ h₂ h₇ h₈ G hGmin M hM E hEM hsd p r hp hr
      hpτ P hPE hPcard R hRCE hRcard q a hq V hVCent hVcard hRnormV hQne T hT hNT
  have hTM : T ≠ M := fun h => hnonconj 1 (by rw [Prep09.conjSub_one]; exact h)
  have hrσM : r ∉ sigmaPrimes M := notMem_sigmaPrimes_of_mem_tau1Primes hrτM
  have hqr : q ≠ r := fun h => hrσM (h ▸ hqσM)
  have hVS : V ≤ sigmaCore M := hVCent.trans inf_le_left
  have hVcP : V ≤ centralizer (P : Set G) := hVCent.trans inf_le_right
  have hRE : R ≤ E := hRCE.trans inf_le_left
  have hQV : (⁅V, R⁆ : Subgroup G) ≤ V := commutator_le_left_of_le_normalizer hRnormV
  have hQM : (⁅V, R⁆ : Subgroup G) ≤ M := (hQV.trans hVS).trans (sigmaCore_le M)
  have hQpg : IsPGroup q ↥(⁅V, R⁆ : Subgroup G) := (IsPGroup.of_card hVcard).to_le hQV
  have hsetup : Prep08.IsRegularTauOneAlphaSetup M R (⁅V, R⁆ : Subgroup G) r q :=
    { isCoatom_M := hM
      mem_tau1 := hrτM
      prime_q := hq
      q_ne := hqr
      q_notMem_alpha := hqαM
      le_P := hRE.trans hEM
      natCard_P := hRcard
      le_Q := hQM
      Q_ne_bot := hQne
      isPGroup_Q := hQpg
      normalized := hRnormQ
      centralizer_eq := hCQR
      not_unique := by
        rw [huniq.setOf_eq_singleton]
        exact fun h => hTM (Set.singleton_eq_singleton_iff.1 h) }
  obtain ⟨hCARne, hfix⟩ :=
    inf_alphaCoreOf_centralizer_fixed_points hG.nonabelian hG.odd hG.solvable hsetup hAMne
  have hD : Prep06.alphaCoreIn M ⊓ centralizer (P : Set G) =
      Prep06.alphaCoreIn M ⊓ centralizer (R : Set G) := hadm hrτM (hdisj.resolve_left hqαM)
  set D : Subgroup G := Prep06.alphaCoreIn M ⊓ centralizer (P : Set G) with hDdef
  have hDA : D ≤ Prep08.alphaCoreOf M := inf_le_left
  have hDR : D ≤ centralizer (R : Set G) := hD ▸ inf_le_right
  have hVM : V ≤ M := hVS.trans (sigmaCore_le M)
  have hVnormA : V ≤ normalizer ((Prep06.alphaCoreIn M : Subgroup G) : Set G) :=
    hVM.trans (le_normalizer_map_subtype_of_normal (alphaCore_normal ↥M))
  have hVnormD : V ≤ normalizer ((D : Subgroup G) : Set G) := fun x hx =>
    normalizer_inf_le_normalizer_inf _ _ ⟨hVnormA hx, le_normalizer (hVcP hx)⟩
  have hRcD : R ≤ centralizer (D : Set G) := Subgroup.le_centralizer_iff.1 hDR
  have hQcD : (⁅V, R⁆ : Subgroup G) ≤ centralizer (D : Set G) :=
    commutator_le_centralizer_of_le_normalizer_of_le_centralizer hVnormD hRcD
  have hDQR : D ≤ centralizer (((⁅V, R⁆ ⊔ R : Subgroup G)) : Set G) :=
    Subgroup.le_centralizer_iff.1 (sup_le hQcD hRcD)
  have hDbot : D = ⊥ := le_bot_iff.1 (hfix ▸ le_inf hDA hDQR)
  exact hCARne (by rw [← alphaCoreIn_prep06_eq_alphaCoreOf, ← hD]; exact hDbot)

end

end CFSG.FeitThompson.Proofs
