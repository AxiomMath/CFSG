module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.Lemma1Main
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.Lemma3
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.Case3
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detection

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint Heis

set_option linter.unusedSectionVars false


variable (K : Type) [Field K]

theorem exists_MPart [Finite K] {H : Subgroup (ModGL Tag.E8 K)} (hH : H ≤ adjointGroup Tag.E8 K)
    (hX : XS K ≤ H) (hN : ¬ H ≤ Subgroup.normalizer (XS K : Set (ModGL Tag.E8 K))) :
    MPart K H := by
  obtain ⟨g, hg, p, hp, β, hβ, ⟨w, hw⟩, hdeg, hB, hnot⟩ := lemma1 K hH hX hN
  have hUH : Uθ Tag.E8 K ≤ H := (Uθ_le_X1 K).trans ((X1_le_XS K).trans hX)
  rcases hdeg with h1 | h1 | h1
  · refine case_one K (conjSub_le_of_mem_of_le hg hUH) ?_ hnot
    rw [hB]
    exact conjSub_le_Qθ hp (rootSubgroup_le_Qθ_E8 K ⟨hβ, h1⟩)
  · exact case_three K hH hX hg hp hβ h1 hB hnot
  · have hβ' : β = -theta := deg_eq_neg_two β (mem_rootFinset.2 hβ) h1
    have e : conjSub p (Heis.Uneg Tag.E8 K) = conjSub g (Uθ Tag.E8 K) := by
      rw [hB, hβ']
      rfl
    refine case_two K hX hp ?_ ?_
    · rw [e]
      exact conjSub_le_of_mem_of_le hg hUH
    · rw [e]
      exact hnot

theorem frameDetection_E8 [Finite K] : FrameDetection Tag.E8 K (cosetRoots Tag.E8 4 5) := by
  intro H hH hX hN
  exact lemma3 K hX (exists_MPart K hH hX hN)

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
