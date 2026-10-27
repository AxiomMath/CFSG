module

public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Representations.TypeIIIToVCoherenceFrobeniusPartner
import CFSG.FeitThompson.Representations.TypeThreeFiveFrobeniusPartnerContradiction
import CFSG.FeitThompson.Local.TypePMaximalPrimeFactors
import CFSG.FeitThompson.OddOrder.PairedCompatibleComplements

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem not_isTypeI_and_not_isTypeII_of_isTypeIII_IV_V
    (huniq : ∃! i : Fin 5, CFSG.FeitThompson.localTypes M i)
    (h : IsTypeIII M ∨ IsTypeIV M ∨ IsTypeV M) : ¬ IsTypeI M ∧ ¬ IsTypeII M := by
  refine ⟨fun hI => ?_, fun hII => ?_⟩
  · rcases h with h | h | h
    · have : (0 : Fin 5) = 2 := huniq.unique hI h
      simp at this
    · have : (0 : Fin 5) = 3 := huniq.unique hI h
      simp at this
    · have : (0 : Fin 5) = 4 := huniq.unique hI h
      simp at this
  · rcases h with h | h | h
    · have : (1 : Fin 5) = 2 := huniq.unique hII h
      simp at this
    · have : (1 : Fin 5) = 3 := huniq.unique hII h
      simp at this
    · have : (1 : Fin 5) = 4 := huniq.unique hII h
      simp at this

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

open CFSG.FeitThompson Subgroup

universe u

theorem FPF_type_iii_v_induced_family_noncoherence
    (h₁ : Statements.FBG_five_type_local_classification.{u})
    (h₂ : Statements.FBG_maximal_type_dichotomy.{u})
    (h₃ : Statements.FNI_p_configuration_kappa_factors.{u})
    (h₄ : Statements.FPF_kappa_positive_core_derived_support_disjoint.{u})
    (h₅ : Statements.FPF_non_type_i_sigma_core_identities.{u})
    (h₆ : Statements.FPF_type_iii_v_second_factor_prime.{u})
    (h₇ : Statements.FTS_canonical_signalizer_full_support_coprimality.{u})
    (h₈ : Statements.FTS_canonical_signalizer_structure.{u})
    (h₉ : Statements.FTS_type_II_extended_support_ti.{u}) :
    Statements.FPF_type_iii_v_induced_family_noncoherence.{u} := by
  intro G _ _ hG M U W₁ W₂ hM htype hc hcoh
  have hFBG : _root_.CFSG.FeitThompson.IsFBGAmbient G :=
    ⟨hG.odd, hG.simple, hG.nonabelian, hG.solvable⟩
  obtain ⟨hMI, hMII⟩ :=
    not_isTypeI_and_not_isTypeII_of_isTypeIII_IV_V ((h₁ G hFBG).1 M hM) htype
  obtain ⟨S, T₀, V₁, V₂, hpair⟩ := (h₂ G hFBG).2.resolve_left fun hall => hMI (hall M hM)
  obtain ⟨N₀, A, B, hpM⟩ := hpair.exists_fst_eq hM hMI
  obtain ⟨N, hpair'⟩ := hpM.exists_isTypePPair_of_isWitnessedPConfiguration hc
  obtain ⟨E, -, hcN, -⟩ := hpair'.exists_compatible_right
  have hNII : IsTypeII N := hpair'.typeII.resolve_left hMII
  have hfree := FPF_type_iii_v_coherence_forces_frobenius_partner h₁ h₃ h₄ h₅ h₆ h₇ h₈ h₉
    G hG M U W₁ W₂ hM htype hc hcoh N E hpair'.isCoatom_right hNII hcN
  exact FPF_type_iii_v_frobenius_partner_contradiction h₃ h₅ h₆ h₇ h₈
    G hG M U W₁ W₂ hM htype hc N E hpair'.isCoatom_right hNII hcN hfree hcoh

end CFSG.FeitThompson.Proofs

end
