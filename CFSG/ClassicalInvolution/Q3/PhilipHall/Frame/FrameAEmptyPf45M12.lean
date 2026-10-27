module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf45M12One
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf45M12Tight
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoFoundation

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ComponentClassification.AS76b

section Target



@[expose] def FrameC201M12FalseB : Prop :=
  ∀ (T : Type) [Group T] [Finite T] [CaseIAmbient T], Thm3A.Thm3RBelowG (Nat.card T) →
    ∀ (R : Subgroup T) (t : T) (J : Subgroup T) (zK zJ : T), FrameCaseIHyps T R t J zK zJ →
      ∀ H : Subgroup T, omegaGen (aStar (CoreAssembly.conjClass R) R) = H →
        Thm3RowM12 (⊤ : Subgroup ↥H) → False

theorem frameC201M12False_of_rows
    (h4 : Asc75Theorem4)
    (h39 : Lemma39FStar) : FrameC201M12FalseB := by
  intro T _ _ _ hT R t J zK zJ hh H hH hrow
  obtain rfl : t = zK := hh.datum.unique.eq hh.viol.hzK
  have hs : M12Std R t J zJ H :=
    ⟨⟨hh.nonabelian, hh.datum, hh.viol, hh.ne, hT⟩, hH, hrow⟩
  obtain ⟨S, cfg⟩ := m12_cfg_exists hs
  by_cases hm1 : sigmaNorm R ≤ Subgroup.normalizer (firstFactor R : Set T)
  · exact cfg.false_of_m1 h39 hm1
  · exact cfg.false_of_gt_one h4 hm1

end Target

section Certs


theorem frameC201M12False_of_certs : FrameC201M12FalseB :=
  frameC201M12False_of_rows CFSG.ComponentClassification.RankTwoFoundation.asc75Theorem4
    lemma39FStar_of_certs

end Certs

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
