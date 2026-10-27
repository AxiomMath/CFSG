module

public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
import CFSG.FeitThompson.Representations.TypeThreeFourInnerComplementCyclic
import CFSG.FeitThompson.Representations.ReciprocalTypeThreeLowFamilyBound
import CFSG.FeitThompson.Local.TypePInnerActionFaithful
import CFSG.FeitThompson.Local.PCoreLinearAlternativePConfiguration
import CFSG.FeitThompson.Local.PairedSupportingCrossedAlternatives
import CFSG.FeitThompson.OddOrder.NormQuotientDegreeComparison

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson.Proofs

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson.Prep05

universe u

theorem FPF_ordered_reciprocal_maxima_type_two
    (h₁ : Statements.FCH_type_p_action_kernel_ratio.{u})
    (h₂ : Statements.FCH_type_p_actual_bridge_remainder.{u})
    (h₃ : Statements.FNI_type_p_elementary_core_structure.{u})
    (h₄ : Statements.FNI_type_p_prime_factors.{u})
    (h₅ : Statements.FPF_type_iii_full_support_ti_induction.{u})
    (h₆ : Statements.FPF_type_iii_iv_core_elementary_chief_kernel_trivial.{u})
    (h₇ : Statements.FPF_type_iii_iv_second_derived_fitting.{u})
    (h₈ : Statements.FPF_type_iii_v_extended_dade_support.{u})
    (h₉ : Statements.FPF_type_iii_v_induced_family_noncoherence.{u})
    (h₁₀ : Statements.FPF_type_iii_v_second_factor_prime.{u}) :
    Statements.FPF_ordered_reciprocal_maxima_type_two.{u} := by
  intro G _ _ hG S T U V W₁ W₂ hS hT hcS hcT hlt
  have hG₆ : _root_.CFSG.FeitThompson.Prep06.IsMinimalOddSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  set p := Nat.card ↥W₂ with hp
  set q := Nat.card ↥W₁ with hq
  have hSII : IsTypeII S := by
    rcases (h₃ G hG S U W₁ W₂ hS hcS p q rfl rfl).1 with h | h
    · exact h
    · have := Fintype.ofFinite G
      exact absurd hlt (not_lt.2 (FPF_type_iii_iv_inner_complement_cyclic h₆ h₇ h₈ h₉ h₁₀
        G hG₆ S U W₁ W₂ hS (Or.inl h) hcS).2.1.le)
  refine ⟨hSII, ?_⟩
  obtain ⟨-, hpp, hqq, hop, hoq, -, -, -, -, -, -, -, hmod, -⟩ :=
    h₃ G hG S U W₁ W₂ hS hcS p q rfl rfl
  rcases (h₃ G hG T V W₂ W₁ hT hcT q p rfl rfl).1 with hTII | hTIII
  · exact hTII
  exfalso
  obtain ⟨Vm, _, _, -, ⟨e⟩⟩ := hmod
  obtain ⟨hCbot, -⟩ := FNI_type_p_inner_action_faithful.{u} h₁ h₃ G hG S U W₁ W₂ hS hcS
  have hSnorm : S ≤ normalizer ((hallCoreOf S : Subgroup G) : Set G) :=
    le_normalizer_map_subtype_hallCore S
  have hule := (FNI_type_p_core_linear_alternative.{u, u} h₃ G hG S U W₁ W₂ hS hcS p q
    ((centralizerIn U (hallCoreOf S)).relIndex U) ((p ^ q - 1) / (p - 1)) rfl rfl rfl rfl
    Vm e (conjLinear p hSnorm e) (isConjModule_conjLinear p hSnorm e) _ _ rfl
    rfl).2.2.2.2.2.2.2.2.2.2
  rw [hCbot, Subgroup.relIndex_bot_left, ← Nat.geomSum_eq hpp.two_le] at hule
  have hv := natCard_reciprocal_complement h₁ h₃ hG T V W₁ W₂ hT hcT hlt
  rw [← Nat.geomSum_eq hqq.two_le] at hv
  have hstrict := sub_one_div_lt_sub_one_div_of_odd_prime_lt hpp hqq hop hoq hlt
    (u := (Nat.card ↥U : ℝ)) (v := (Nat.card ↥V : ℝ))
    (by exact_mod_cast (Nat.card_pos : 0 < Nat.card ↥U))
    (by exact_mod_cast hule) (by rw [hv]; push_cast; rfl)
  have hle := FPF_reciprocal_type_three_low_family_bound h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀
    G hG S T U V W₁ W₂ hS hT hcS hcT p q _ _ rfl rfl rfl rfl hlt hTIII
  have hleR := (Rat.cast_le (K := ℝ)).2 hle
  push_cast at hleR
  linarith

end CFSG.FeitThompson.Proofs

end
