module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Hyp
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Frame
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Defs
import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Step1
import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.Quasi
import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.Central
import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.PureA
import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.MElement
import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.EqTop
import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingF4EvenAux11

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

set_option linter.unusedSectionVars false


theorem twClosing_f4Six_even (K : Type) [Field K] [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    (D : LangLevi TwClass.f4Six.tag K TwClass.f4Six.w) :
    TwFrameClosing TwClass.f4Six.tag K (TwClass.f4Six.X₁ D ⊔ TwClass.f4Six.X₂ D) := by
  have hK3 : 3 ≤ Nat.card K := by omega
  have hKq : TwClass.f4Six.minQ ≤ Nat.card K := hK3
  have hq := twQuasi_of_ne_e6Six TwClass.f4Six (by decide) K hKq D
  have hb := TwBasicAux.twBasic_of_quasi TwClass.f4Six D hq.1
  have hc := twCentral TwClass.f4Six K hKq D
  have hco := twCoords TwClass.f4Six K hKq D
  have hp := twPure_A TwClass.f4Six (by decide) K hKq D
  intro H hHG hXH hN
  obtain ⟨g, hgH, hgX⟩ := exists_conj_not_le hb hq hc hHG hXH hN
  obtain ⟨m, hmH, hmQ, hmV⟩ := exists_M_element hb hc hco hp hK3 hHG hXH hgH hgX
  have hXX₁ : TwClass.f4Six.X₁ D ≤ TwClass.f4Six.X₁ D ⊔ TwClass.f4Six.X₂ D := le_sup_left
  have hXX₂ : TwClass.f4Six.X₂ D ≤ TwClass.f4Six.X₁ D ⊔ TwClass.f4Six.X₂ D := le_sup_right
  have hX₁ : TwClass.f4Six.X₁ D ≤ H := hXX₁.trans hXH
  have hX₂ : TwClass.f4Six.X₂ D ≤ H := hXX₂.trans hXH
  have hmX : m ∉ TwClass.f4Six.X₁ D := fun hm =>
    hmV (Submodule.subset_span ⟨m, ⟨hXX₁ hm, hmQ⟩, rfl⟩)
  have hQ := F4Even.Qθ_le_of_notmem D hK3 hHG hX₁ hX₂ hmH hmQ hmX
  exact eq_top_of_Qθ_Uneg_le_of_any _ K hHG hQ (hb.Uneg_le.trans hX₁)

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
