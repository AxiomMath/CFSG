module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf43L3E8End
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf43L3E8CentLe
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf43Sigma
public import CFSG.LocalAnalysis.ComponentClassification.Asc75Theorem3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3

section CfgExists

variable {T : Type} [Group T] [Finite T]
  {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T} {H : Subgroup T}

theorem l3e8_cfg_exists (hs : L3E8Std K z J zJ H) :
    ∃ Q E S : Subgroup T, L3E8Cfg K z J zJ H Q E S := by
  obtain ⟨S, cfg⟩ := frameCfg_exists hs.toFrameStd
  have hfaith := l3e8_faithful hs
  exact ⟨oddTwoCoreIn (firstFactor K), oddTwoCoreIn (firstFactor K) ⊓ S, S,
    { toFrameQCfg := frameQCfg_of cfg
      hH := hs.hH
      row := hs.row
      faithful := hfaith }⟩

end CfgExists

section Target

@[expose] def FrameC201L3E8FalseB : Prop :=
  ∀ (T : Type) [Group T] [Finite T] [CaseIAmbient T], Thm3A.Thm3RBelowG (Nat.card T) →
    ∀ (R : Subgroup T) (t : T) (J : Subgroup T) (zK zJ : T), FrameCaseIHyps T R t J zK zJ →
      ∀ H : Subgroup T, omegaGen (aStar (CoreAssembly.conjClass R) R) = H →
        Thm3RowL3E8 (⊤ : Subgroup ↥H) → False

theorem frameC201L3E8False_of_rows
    (_h3 : CFSG.ComponentClassification.AschbacherTheorem3.Theorem3Statement)
    (h39 : Lemma39FStar) : FrameC201L3E8FalseB := by
  intro T _ _ _ hT R t J zK zJ hh H hH hrow
  obtain rfl : t = zK := hh.datum.unique.eq hh.viol.hzK
  have hs : L3E8Std R t J zJ H :=
    ⟨⟨hh.nonabelian, hh.datum, hh.viol, hh.ne, hT⟩, hH, hrow⟩
  obtain ⟨Q, E, S, cfg⟩ := l3e8_cfg_exists hs
  exact l3e8_endgame h39 cfg (l3e8_cent_le cfg cfg.unique_coset hh.cit hh.pkg)

end Target

section Certs

theorem frameC201L3E8False_of_certs : FrameC201L3E8FalseB :=
  frameC201L3E8False_of_rows CFSG.ComponentClassification.AschbacherTheorem3.theorem_3_holds
    lemma39FStar_of_certs

end Certs

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
