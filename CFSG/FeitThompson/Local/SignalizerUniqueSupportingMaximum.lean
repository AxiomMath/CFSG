module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.NonregularComplementElementTauTwoPrimes
import CFSG.FeitThompson.Local.TauTwoSubgroupCentralizerUnique
public import CFSG.FeitThompson.Definitions.KernelFilteredIrreducibleCharacters

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson
open CFSG.FeitThompson.Prep09

universe u

theorem exists_isUniqueMaximalOvergroup_centralizer_of_mem_sigmaSupportingMaximals
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_tau_two_hall_abelian.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_tau12_fixed_plane_line_core_free.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FNI_tau13_nonfree_third_factor_structure.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_plane_maximal_overgroups.{u})
    (h₉ : _root_.CFSG.FeitThompson.Statements.FTS_signalizer_auxiliary_prime_support.{u})
    {G : Type u} [Group G] [Finite G] (hG : IsMinimalSimpleOddOrder G)
    {x : G} (hx : x ∈ sigmaSupport G) (hk : 1 < sigmaMultiplicity x)
    {M : Subgroup G} (hM : M ∈ sigmaSupportingMaximals x) :
    ∃ T : Subgroup G, IsUniqueMaximalOvergroup (centralizer ({x} : Set G)) T ∧
      sigmaSignalizer x = centIn (sigmaCore T) {x} ∧ centIn (sigmaCore T) {x} ≠ ⊥ ∧
      (∀ p : ℕ, p.Prime → p ∣ orderOf x → p ∈ tauTwoPrimes T) ∧
      T ≠ M ∧ x ∈ M ⊓ T ∧ FreeCore.IsInternalSemidirectProduct T (sigmaCore T) (M ⊓ T) ∧
      sigmaPrimes T ∩ sigmaPrimes M = ∅ ∧ tauTwoPrimes T ⊆ sigmaPrimes M ∧
      (∀ p ∈ sigmaPrimes T, p ∣ Nat.card M → p ∈ betaPrimes T) := by
  obtain ⟨-, -, -, hx1⟩ := mem_sigmaSupport.1 hx
  obtain ⟨q, hqp, hqx, -, -, -, T, hTco, hTM, -, -, hxMT, hsd, hσ, hqτ, hτσ, hβ, hRx, hRne⟩ :=
    h₉ G hG x hx hk M hM
  have hFT : IsFTAmbient G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
  have hord : orderOf x ≠ 0 := (orderOf_pos x).ne'
  have hprimes : ∀ r ∈ (orderOf x).primeFactors, r ∈ tauTwoPrimes T :=
    FTS_core_nonregular_element_with_tau_two_prime h₁ h₄ h₅ h₆ h₇ h₈ G hFT T hTco (M ⊓ T)
      inf_le_right hsd x hxMT hx1 hRne ⟨q, Nat.mem_primeFactors.2 ⟨hqp, hqx, hord⟩, hqτ⟩
  have hprimes' : ∀ p : ℕ, p.Prime → p ∣ orderOf x → p ∈ tauTwoPrimes T := fun p hp hpd =>
    hprimes p (Nat.mem_primeFactors.2 ⟨hp, hpd, hord⟩)
  have hXle : (zpowers x : Subgroup G) ≤ T := zpowers_le.2 (Subgroup.mem_inf.1 hxMT).2
  have hXne : (zpowers x : Subgroup G) ≠ ⊥ := fun h => hx1 (zpowers_eq_bot.1 h)
  have hXτ : ∀ s ∈ (Nat.card ↥(zpowers x : Subgroup G)).primeFactors, s ∈ tauTwoPrimes T := by
    intro s hs
    rw [Nat.card_zpowers] at hs
    exact hprimes s hs
  have hcent : centIn (sigmaCore T) ((zpowers x : Subgroup G) : Set G) ≠ ⊥ := by
    rw [centIn_def, centralizer_coe_zpowers, ← centIn_def]
    exact hRne
  obtain ⟨-, huniq⟩ := FTS_tau_two_subgroup_centralizer_unique h₂ h₃ G hG T hTco
    (zpowers x) hXle hXne hXτ hcent
  rw [centralizer_coe_zpowers] at huniq
  exact ⟨T, huniq, hRx, hRne, hprimes', hTM, hxMT, hsd, hσ, hτσ, hβ⟩

theorem FTS_signalizer_unique_supporting_maximum
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_tau_two_hall_abelian.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_tau12_fixed_plane_line_core_free.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FNI_tau13_nonfree_third_factor_structure.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_plane_maximal_overgroups.{u})
    (h₉ : _root_.CFSG.FeitThompson.Statements.FTS_signalizer_auxiliary_prime_support.{u}) :
    _root_.CFSG.FeitThompson.Statements.FTS_signalizer_unique_supporting_maximum.{u} := by
  intro G _ _ hG x hx hk
  obtain ⟨M₀, hM₀co, hM₀x, -⟩ := mem_sigmaSupport.1 hx
  have hM₀ : M₀ ∈ sigmaSupportingMaximals (G := G) x := mem_sigmaSupportingMaximals.2 ⟨hM₀co, hM₀x⟩
  obtain ⟨T₀, hT₀uniq, hRx₀, hRne₀, hprimes₀, -⟩ :=
    exists_isUniqueMaximalOvergroup_centralizer_of_mem_sigmaSupportingMaximals
      h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ hG hx hk hM₀
  refine ⟨⟨T₀, ⟨hT₀uniq.isCoatom, hT₀uniq.le⟩, fun T hT => hT₀uniq.eq_of_isCoatom hT.1 hT.2⟩,
    fun T hTco hTle => ?_⟩
  have hTT₀ : T = T₀ := hT₀uniq.eq_of_isCoatom hTco hTle
  subst hTT₀
  refine ⟨hRx₀, hRne₀, hprimes₀, fun M hM => ?_⟩
  obtain ⟨T', hT'uniq, -, -, -, hTM, hxMT, hsd, hσ, hτσ, hβ⟩ :=
    exists_isUniqueMaximalOvergroup_centralizer_of_mem_sigmaSupportingMaximals
      h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ hG hx hk hM
  have hT'T : T' = T := hT'uniq.unique hT₀uniq
  subst hT'T
  exact ⟨hTM, hxMT, hsd, hσ, hτσ, hβ⟩

end

end CFSG.FeitThompson.Proofs
