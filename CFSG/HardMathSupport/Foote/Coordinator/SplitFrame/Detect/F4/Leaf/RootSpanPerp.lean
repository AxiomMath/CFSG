module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.CentralizerData
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.RootSpanInter
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.Defs
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectionF4

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint

set_option linter.unusedSectionVars false



theorem rootSpan_inf_perp_F4 (K : Type) [Field K] :
    rootSpan Tag.F4 K (parabolicPosRoots Tag.F4 (Heis.Jθ Tag.F4)) ⊓
      rootSpan Tag.F4 K ((fun β => w₁ • β) '' parabolicPosRoots Tag.F4 (Heis.Jθ Tag.F4)) ≤
    rootSpan Tag.F4 K (parabolicPosRoots Tag.F4 (Heis.Jθ Tag.F4) ∩
      ((fun β => w₁ • β) '' parabolicPosRoots Tag.F4 (Heis.Jθ Tag.F4))) := by
  refine rootSpan_inf_rootSpan_image_smul_le K w₁ (fun α hα => hα.2)
    (fun α hα β hβ a b ha hb hr => add_mem_parabolicPosRoots hα hβ ha hb hr) ?_
  rintro β ⟨⟨hr, h0⟩, -, hp⟩
  rw [w₁, wordProd_smul_eq_foldr]
  exact leviWord_min β (mem_rootFinset.2 hr) (h0 (Heis.iθ Tag.F4) (by simp [Heis.Jθ])) hp


end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4
