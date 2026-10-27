module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.OddOrder.MinimalCounterexampleSimple
import CFSG.FeitThompson.OddOrder.NoMinimalSimpleGroupOddOrder

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson

universe u

theorem FT_odd_order_solvable
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_maximal_type_dichotomy.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FPF_ordered_pair_exclusion.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FPF_type_I_frobenius.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_canonical_signalizer_structure.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_sigma_prime_separation.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_core_kappa_identity.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_dade_support.{u}) :
    _root_.CFSG.FeitThompson.Statements.FT_odd_order_solvable.{u} := by
  intro G _ _ hodd
  exact isSolvable_of_odd_natCard_of_no_minimal_simple'
    (fun H _ _ hHodd hsimple hnonabelian hsolvable =>
      FT_no_minimal_odd_simple h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ H
        ⟨hHodd, hsimple, hnonabelian, hsolvable⟩) hodd

end

end CFSG.FeitThompson.Proofs
