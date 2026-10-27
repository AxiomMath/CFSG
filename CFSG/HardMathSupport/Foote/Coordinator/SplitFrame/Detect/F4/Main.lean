module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.Lemma3
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.Case3

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint Heis

set_option linter.unusedSectionVars false


variable (K : Type) [Field K]

theorem exists_MPart [Finite K] {H : Subgroup (ModGL Tag.F4 K)} (hH : H ≤ adjointGroup Tag.F4 K)
    (hX : XS K ≤ H) (hN : ¬ H ≤ Subgroup.normalizer (XS K : Set (ModGL Tag.F4 K))) :
    MPart K H := by
  obtain ⟨g, hg, p, hp, β, hβ, ⟨w, hw⟩, hdeg, hB, hnot⟩ := lemma1 K hH hX hN
  have hUH : Uθ Tag.F4 K ≤ H := (Uθ_le_X1 K).trans ((X1_le_XS K).trans hX)
  rcases hdeg with h1 | h1 | h1
  · refine case_one K (conjSub_le_of_mem_of_le hg hUH) ?_ hnot
    rw [hB]
    exact conjSub_le_Qθ K hp (rootSubgroup_le_Qθ K ⟨hβ, h1⟩)
  · refine case_three K hH hX hg hp hβ ?_ h1 hB hnot
    rw [hw]
    exact isLongRoot_smul_highRoot Tag.F4 w
  · have hβ' : β = -theta := deg_eq_neg_two β (mem_rootFinset.2 hβ) h1
    have e : conjSub p (Heis.Uneg Tag.F4 K) = conjSub g (Uθ Tag.F4 K) := by
      rw [hB, hβ']
      rfl
    refine case_two K hX hp ?_ ?_
    · rw [e]
      exact conjSub_le_of_mem_of_le hg hUH
    · rw [e]
      exact hnot

theorem frameDetection_F4 [Finite K] (hK : 3 ≤ Nat.card K) :
    FrameDetection Tag.F4 K (cosetRoots Tag.F4 1 3) := by
  intro H hH hX hN
  exact lemma3 K hK hX (exists_MPart K hH hX hN)

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4
