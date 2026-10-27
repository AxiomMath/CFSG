module

public import CFSG.ClassicalInvolution.Q3.TL4InductDefs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSetCore

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3

section Cases

@[expose] def TwinCoreDiscPerpSP (n : ℕ) : Prop :=
  CIT3Below n → CFSG.ClassicalInvolution.Q3.TL4.TightBelowRPlus 3 n → TwinCoreDiscPerpS' n

theorem twinStepRSE_of_cases {n : ℕ} (hA : CIT3Below n → CFSG.ClassicalInvolution.Q3.TL4.TightBelowRPlus 3 n → TwinCoreConnSE' n)
    (hB : TwinCoreDiscPerpSP n)
    (hC : CIT3Below n → CFSG.ClassicalInvolution.Q3.TL4.TightBelowRPlus 3 n → TwinCorePerpSE' n)
    (hL : Thm1RTwinLiftSetEBelow n) :
    CIT3Below n → CFSG.ClassicalInvolution.Q3.TL4.TightBelowRPlus 3 n → (3 : ℕ) = 3 →
      Thm1RTwinLiftSetEBelow (n + 1) :=
  fun hcit hP _ => thm1RTwinLiftSetEBelow_succ hL
    (thm1RTwinCoreAtSE_of_cases (hA hcit hP) (hB hcit hP) (hC hcit hP) hcit
      (CFSG.ClassicalInvolution.Q3.TL4.tightBelow_of_plus hP) hL.toSet)

end Cases

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
