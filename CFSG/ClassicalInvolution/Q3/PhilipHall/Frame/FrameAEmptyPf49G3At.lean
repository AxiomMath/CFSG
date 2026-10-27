module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf49G3Defs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ComponentClassification.AS76b

namespace Thm3A

section Theorem

@[expose] def Thm3RAtG (m : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nat.card X = m → classicalInvolutionOddCore X = ⊥ →
    ∀ Φ : Set (Subgroup X), TypeRHyp Φ → ∀ K ∈ Φ, ¬ AEmpty Φ K → Thm3RConclG Φ K

@[expose] def Thm3RBelowG (n : ℕ) : Prop := ∀ m < n, Thm3RAtG m

@[expose] def Thm3RStepG (m : ℕ) : Prop :=
  CIT3Below (m + 1) → TL4.TightBelowRPlus 3 (m + 1) → Thm3RBelowG m → Thm3RAtG m

theorem thm3RBelowG_of_step_below (hstep : ∀ m, Thm3RStepG m) {N : ℕ} (hc : CIT3Below N)
    (hp : TL4.TightBelowRPlus 3 N) : Thm3RBelowG N := by
  have key : ∀ m, m < N → Thm3RAtG m := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm
      exact hstep m (CIT3Below.mono (Nat.succ_le_of_lt hm) hc)
        (hp.mono (Nat.succ_le_of_lt hm)) (fun k hk => ih k hk (lt_trans hk hm))
  exact key

end Theorem

end Thm3A

section Cases

@[expose] def FrameCaseITG : Prop :=
  ∀ (T : Type) [Group T] [Finite T] [IsSimpleGroup T], Thm3A.Thm3RBelowG (Nat.card T) →
    (∃ a b : T, a * b ≠ b * a) → CIT3Below (Nat.card T) →
    TL4.TightBelowRPlus 3 (Nat.card T) → ¬ TwoSubgroupsFourGenerated T →
    ∀ (R : Subgroup T) (t : T), FrameTightDatum R t →
      ∀ (J : Subgroup T) (zK zJ : T), AViol (CoreAssembly.conjClass R) R J zK zJ →
        aStar (CoreAssembly.conjClass R) R ≠ CoreAssembly.conjClass R → False

@[expose] def FrameCaseIITG : Prop :=
  ∀ (T : Type) [Group T] [Finite T] [IsSimpleGroup T], Thm3A.Thm3RBelowG (Nat.card T) →
    (∃ a b : T, a * b ≠ b * a) → CIT3Below (Nat.card T) →
    TL4.TightBelowRPlus 3 (Nat.card T) → ¬ TwoSubgroupsFourGenerated T →
    ∀ (R : Subgroup T) (t : T), FrameTightDatum R t →
      ∀ (J : Subgroup T) (zK zJ a g : T),
        AViol (CoreAssembly.conjClass R) R J zK zJ →
        a ∈ pairNormalizers R J zK zJ → a * zJ * a⁻¹ = zK → conjSub a J ≠ R →
        conjSub g R = conjSub a J → g * zK * g⁻¹ = zK →
        aStar (CoreAssembly.conjClass R) R = CoreAssembly.conjClass R → False

theorem frameAEmptyP_of_casesTG (hstep : ∀ m, Thm3A.Thm3RStepG m) (h1 : FrameCaseITG)
    (h2 : FrameCaseIITG) : FrameAEmptyP := by
  refine frameAEmptyP_of_cases ?_ ?_
  · intro T _ _ _ hnab hB hP hl R t hD J zK zJ hv hs
    exact h1 T (Thm3A.thm3RBelowG_of_step_below hstep hB hP) hnab hB hP hl R t hD J zK zJ hv hs
  · intro T _ _ _ hnab hB hP hl R t hD J zK zJ a g hv ha hac hne hg hgK hs
    exact h2 T (Thm3A.thm3RBelowG_of_step_below hstep hB hP) hnab hB hP hl R t hD J zK zJ a g hv
      ha hac hne hg hgK hs

end Cases

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
