module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf47WEnd
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XMain
public import CFSG.LocalAnalysis.ComponentClassification.Asc76L28

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3

section Target



@[expose] def FrameC201WFalseB : Prop :=
  ∀ (T : Type) [Group T] [Finite T] [CaseIAmbient T], Thm3A.Thm3RBelowG (Nat.card T) →
    ∀ (R : Subgroup T) (t : T) (J : Subgroup T) (zK zJ : T), FrameCaseIHyps T R t J zK zJ →
      ∀ H : Subgroup T, omegaGen (aStar (CoreAssembly.conjClass R) R) = H →
        Thm3RowW (restrictFamily (CoreAssembly.conjClass R) H) (⊤ : Subgroup ↥H) → False

theorem frameC201WFalse_of_rows (h1 : CFSG.ComponentClassification.Asc76.Asc76Theorem1) :
    FrameC201WFalseB := by
  intro T _ _ _ hT R t J zK zJ hh H hH hrow
  obtain rfl : t = zK := hh.datum.unique.eq hh.viol.hzK
  have hs : WStd R t J zJ H :=
    ⟨⟨hh.nonabelian, hh.datum, hh.viol, hh.ne, hT⟩, hH, hrow⟩
  obtain ⟨S, cfg⟩ := w_cfg_exists hs
  exact cfg.false_of_thm1 h1

end Target

section Certs


theorem frameC201WFalse_of_certs : FrameC201WFalseB :=
  frameC201WFalse_of_rows
    (CFSG.ComponentClassification.Asc76X.asc76Theorem1_of_lemma28
      CFSG.ComponentClassification.Asc76.asc76Lemma28)

end Certs

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
