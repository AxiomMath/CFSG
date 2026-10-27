module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Defs
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Step1
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.MElement
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.EqTop

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

set_option linter.unusedSectionVars false


variable {τ : Tag} {K : Type} [Field K]

theorem theoremA {X₁ X₂ : Subgroup (ModGL τ K)} (h : TwFrameHyp X₁ X₂) :
    TwFrameClosing τ K (X₁ ⊔ X₂) := by
  intro H hHG hXH hN
  obtain ⟨g, hgH, hgX⟩ := exists_conj_not_le h.basic h.quasi h.central hHG hXH hN
  obtain ⟨m, hmH, hmQ, hmS⟩ := exists_M_element h.basic h.central h.coords h.pure h.three_le
    hHG hXH hgH hgX
  have hQ := Qθ_le_of_M_element h hXH hmH hmQ hmS
  exact eq_top_of_Qθ_Uneg_le τ K h.three_le hHG hQ (h.basic.Uneg_le.trans (le_sup_left.trans hXH))

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
