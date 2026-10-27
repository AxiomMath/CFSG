module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.SharedRecog
public import CFSG.ClassicalInvolution.Q3.TL4InductDefs
public import CFSG.ClassicalInvolution.Q3.Q3T6DConj

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

namespace FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected.AschTight

section Targets

@[expose] def FrameAEmptyP : Prop :=
  ∀ (T : Type) [Group T] [Finite T] [IsSimpleGroup T], (∃ a b : T, a * b ≠ b * a) →
    CIT3Below (Nat.card T) → TL4.TightBelowRPlus 3 (Nat.card T) → ¬ TwoSubgroupsFourGenerated T →
    ∀ (R : Subgroup T) (t : T), FrameTightDatum R t → AEmpty (CoreAssembly.conjClass R) R

theorem frameAEmpty_of_frameAEmptyP (h : FrameAEmptyP)
    (hplus : ∀ n, CIT3Below n → TL4.TightBelowRPlus 3 n) : FrameAEmpty :=
  fun T _ _ _ hnab hB _ hl R t hD => h T hnab hB (hplus _ hB) hl R t hD

@[expose] def FrameNoSwapP : Prop :=
  ∀ (T : Type) [Group T] [Finite T] [IsSimpleGroup T], (∃ a b : T, a * b ≠ b * a) →
    CIT3Below (Nat.card T) → TL4.TightBelowRPlus 3 (Nat.card T) → ¬ TwoSubgroupsFourGenerated T →
    ∀ (R : Subgroup T) (t : T), FrameTightDatum R t →
      ∀ (J : Subgroup T) (zK zJ a g : T),
        AViol (CoreAssembly.conjClass R) R J zK zJ →
        a ∈ pairNormalizers R J zK zJ → a * zJ * a⁻¹ = zK → conjSub a J ≠ R →
        conjSub g R = conjSub a J → g * zK * g⁻¹ = zK → False

theorem frameAEmptyP_of_noSwapP (h : FrameNoSwapP) : FrameAEmptyP := by
  intro T _ _ _ hnab hB hP hl R t hD
  by_contra hn
  obtain ⟨J, zK, zJ, hv⟩ := not_aEmpty_iff.mp hn
  obtain ⟨a, ha, hac, -, -, hne, g, hg, hgK⟩ :=
    Q3T6D.AViol.exists_swap hD.hyp (CoreAssembly.mem_conjClass_self R)
      (fun M hM => by obtain ⟨g, rfl⟩ := hM; exact ⟨g, rfl⟩) hv
  exact h T hnab hB hP hl R t hD J zK zJ a g hv ha hac hne hgK hg

@[expose] def FrameCaseI : Prop :=
  ∀ (T : Type) [Group T] [Finite T] [IsSimpleGroup T], (∃ a b : T, a * b ≠ b * a) →
    CIT3Below (Nat.card T) → TL4.TightBelowRPlus 3 (Nat.card T) → ¬ TwoSubgroupsFourGenerated T →
    ∀ (R : Subgroup T) (t : T), FrameTightDatum R t →
      ∀ (J : Subgroup T) (zK zJ : T), AViol (CoreAssembly.conjClass R) R J zK zJ →
        aStar (CoreAssembly.conjClass R) R ≠ CoreAssembly.conjClass R → False

@[expose] def FrameCaseII : Prop :=
  ∀ (T : Type) [Group T] [Finite T] [IsSimpleGroup T], (∃ a b : T, a * b ≠ b * a) →
    CIT3Below (Nat.card T) → TL4.TightBelowRPlus 3 (Nat.card T) → ¬ TwoSubgroupsFourGenerated T →
    ∀ (R : Subgroup T) (t : T), FrameTightDatum R t →
      ∀ (J : Subgroup T) (zK zJ a g : T),
        AViol (CoreAssembly.conjClass R) R J zK zJ →
        a ∈ pairNormalizers R J zK zJ → a * zJ * a⁻¹ = zK → conjSub a J ≠ R →
        conjSub g R = conjSub a J → g * zK * g⁻¹ = zK →
        aStar (CoreAssembly.conjClass R) R = CoreAssembly.conjClass R → False

theorem frameNoSwapP_of_cases (h1 : FrameCaseI) (h2 : FrameCaseII) : FrameNoSwapP := by
  intro T _ _ _ hnab hB hP hl R t hD J zK zJ a g hv ha hac hne hgK hg
  by_cases hs : aStar (CoreAssembly.conjClass R) R = CoreAssembly.conjClass R
  · exact h2 T hnab hB hP hl R t hD J zK zJ a g hv ha hac hne hgK hg hs
  · exact h1 T hnab hB hP hl R t hD J zK zJ hv hs

theorem frameAEmptyP_of_cases (h1 : FrameCaseI) (h2 : FrameCaseII) : FrameAEmptyP :=
  frameAEmptyP_of_noSwapP (frameNoSwapP_of_cases h1 h2)

end Targets

end FrameAEmptyPf

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
