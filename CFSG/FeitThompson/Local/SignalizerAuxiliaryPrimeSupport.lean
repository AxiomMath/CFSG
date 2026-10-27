module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.SignalizerAuxiliaryBase
import CFSG.FeitThompson.Local.SignalizerRegularActionFromBase
import CFSG.FeitThompson.Local.CanonicalSignalizerStructure
import CFSG.FeitThompson.Local.SigmaPrimeNormalizerEmbeddingSylows
import CFSG.FeitThompson.Local.ComplementPlanePrimesOppositeCore
import CFSG.FeitThompson.Local.OppositeSigmaNormalizerBetaSupport
import CFSG.FeitThompson.Local.SigmaOvergroupConjugacy
import CFSG.FeitThompson.Local.CentralizerTransitiveOnMaximalsSigmaCoreQ
public import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson
  CFSG.FeitThompson
  CFSG.FeitThompson.Prep09

universe u

theorem FTS_signalizer_auxiliary_prime_support
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₃ : Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₄ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₅ : Statements.FTS_beta_prime_centralizing_sylow.{u})
    (h₆ : Statements.FTS_outside_sigma_plane_structure.{u})
    (h₇ : Statements.FTS_plane_maximal_overgroups.{u})
    (h₈ : Statements.FTS_sigma_prime_separation.{u}) :
    Statements.FTS_signalizer_auxiliary_prime_support.{u} := by
  intro G _ _ hG x hx hk M hM
  have : Fintype G := Fintype.ofFinite G
  have := hG.isSimpleGroup
  have hG02 : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG07 : IsFTAmbient G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
  have hG08 : Prep08.IsMinimalSimpleOddOrder G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
  obtain ⟨hMco, hxM⟩ := mem_sigmaSupportingMaximals.1 hM
  obtain ⟨-, -, -, hx1⟩ := mem_sigmaSupport.1 hx
  obtain ⟨q, hq, hqdvd, Q, hQx, hQcard, T, hTco, hTM, hQT, hCxT, hxMT, hsd, hsep⟩ :=
    FTS_signalizer_auxiliary_base h₆ h₇ h₈ G hG x hx hk M hM
  have hQM : Q ≤ sigmaCore M := hQx.trans (zpowers_le.2 hxM)
  have hQbot : Q ≠ ⊥ := ne_bot_of_natCard_eq_prime hq hQcard
  have hQpg : IsPGroup q ↥Q := isPGroup_of_natCard_eq_prime hQcard
  have hqM : q ∈ sigmaPrimes M :=
    primeFactors_orderOf_subset_sigmaPrimes hxM q
      (Nat.mem_primeFactors.2 ⟨hq, hqdvd, (orderOf_pos x).ne'⟩)
  have hqT : q ∉ sigmaPrimes T := fun h => Set.eq_empty_iff_forall_notMem.1 hsep q ⟨h, hqM⟩
  have hqτ : q ∈ tauTwoPrimes T :=
    ((FBG_sigma_prime_normalizer_embedding_sylows h₇ G hG02 M T hMco hTco hTM.symm q hq hqM Q
      (hQM.trans (sigmaCore_le M)) hQbot hQpg hQT).2.2).resolve_left hqT
  have hτσ : tauTwoPrimes T ⊆ sigmaPrimes M :=
    FTS_complement_plane_primes_in_opposite_core h₄ h₆ h₇ G hG07 M hMco T hTco hTM.symm hsd
      ⟨x, mem_inf.2 ⟨hxM, hxMT⟩, hx1⟩
  have hβ : ∀ p ∈ sigmaPrimes T, p ∣ Nat.card ↥M → p ∈ betaPrimes ↥T := fun p hpT hpM =>
    FTS_opposite_sigma_normalizer_beta_support h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ G hG08 M T Q q
      hMco hTco hTM.symm hq hqM (hQM.trans (sigmaCore_le M)) hQbot hQpg hQT hqT p
      (prime_of_mem_sigmaPrimes hpT) hpM hpT
  have hQprime : (Nat.card ↥Q).Prime := by rw [hQcard]; exact hq
  have hCQ : centralizer (Q : Set G) ≤ T := (Subgroup.centralizer_le_normalizer _).trans hQT
  obtain ⟨⟨hR₀C, hR₀norm, hR₀cop⟩, -, -, hR₀card⟩ :=
    FTS_signalizer_regular_action_from_base h₈ G hG x hx M hM T hTco hCxT hxMT hsd
      ⟨Q, hQx, hQprime, hCQ⟩
  have hRR : sigmaSignalizer x = centIn (sigmaCore T) {x} :=
    sigmaSignalizer_eq_of_isNormalHall hR₀C hR₀norm hR₀card hR₀cop
  have hRne : centIn (sigmaCore T) {x} ≠ ⊥ := fun hbot => by
    rw [hbot, Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨1⟩⟩] at hR₀card
    omega
  exact ⟨q, hq, hqdvd, Q, hQx, hQcard, T, hTco, hTM, hQT, hCxT, hxMT, hsd, hsep, hqτ, hτσ, hβ,
    hRR, hRne⟩

end

end CFSG.FeitThompson.Proofs
