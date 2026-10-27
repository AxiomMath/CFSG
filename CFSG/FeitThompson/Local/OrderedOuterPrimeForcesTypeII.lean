module

public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Representations.TypeThreeFourInnerComplementCyclic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson.Proofs

open CFSG.FeitThompson

universe u

theorem FNI_ordered_outer_prime_forces_type_II
    (h₁ : CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    (h₂ : Statements.FPF_type_iii_iv_core_elementary_chief_kernel_trivial.{u})
    (h₃ : Statements.FPF_type_iii_iv_second_derived_fitting.{u})
    (h₄ : Statements.FPF_type_iii_v_extended_dade_support.{u})
    (h₅ : Statements.FPF_type_iii_v_induced_family_noncoherence.{u})
    (h₆ : Statements.FPF_type_iii_v_second_factor_prime.{u}) :
    Statements.FNI_ordered_outer_prime_forces_type_II.{u} := by
  intro G _ _ hG M U W₁ W₂ hM hc hlt
  have hG₅ : CFSG.FeitThompson.Prep05.IsMinimalSimpleOdd G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG₆ : CFSG.FeitThompson.Prep06.IsMinimalOddSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  rcases (h₁ G hG₅ M U W₁ W₂ hM hc _ _ rfl rfl).1 with h | h
  · exact h
  · have := Fintype.ofFinite G
    exact absurd hlt (not_lt.2 (FPF_type_iii_iv_inner_complement_cyclic h₂ h₃ h₄ h₅ h₆
      G hG₆ M U W₁ W₂ hM (Or.inl h) hc).2.1.le)

end CFSG.FeitThompson.Proofs

end
