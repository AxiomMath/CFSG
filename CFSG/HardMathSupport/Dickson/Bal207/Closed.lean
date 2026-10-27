module

public import CFSG.HardMathSupport.Dickson.Bal207.D4GraphWrap
public import CFSG.HardMathSupport.Dickson.Bal207.OrthFam
public import CFSG.HardMathSupport.Dickson.Bal207.OrthFCCases
public import CFSG.HardMathSupport.Dickson.Bal207.OrthSU38Frame
import CFSG.HardMathSupport.Dickson.Bal207.D4EightGriess
import CFSG.HardMathSupport.Dickson.Bal207.OrthD4Comp
import CFSG.HardMathSupport.Dickson.Bal207.OrthFCField
import CFSG.HardMathSupport.Dickson.Bal207.OrthFCGriess
import CFSG.HardMathSupport.Dickson.Bal207.OrthInnerShape
import CFSG.HardMathSupport.Dickson.Bal207.OrthSU38Torus
import CFSG.HardMathSupport.Dickson.Bal207.SU38D4Torus

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourInAux

namespace OrthFix

theorem orthInnerShapeInput_holds : OrthInnerShapeInput := by
  intro F _ _ _ d Q hF hd hQ hT n hdn hn hV t ht
  obtain ⟨hlay, htype, hnorm, hmoved⟩ := orthInnerShape hF hd hQ hT hdn hn hV ht
  refine ⟨hlay, fun L hL => ?_, fun ω hω => hnorm ω hω, hmoved⟩
  obtain ⟨i, hi, -, hiso⟩ := htype L hL
  exact ⟨i, hi, hiso⟩

theorem orthInnerUniqueTwo_holds : OrthInnerUniqueTwo := by
  intro F _ _ _ d Q hF hQ hT n hdn hn hV t ht L L' hL hL'
  exact orthInner_comp_unique_two hF hQ hT hdn hn hV ht hL hL'

theorem orthSU38ToralInput_holds : OrthSU38ToralInput :=
  su38Toral_of_mem_E

end OrthFix

namespace OrthFC

theorem orthInnerCases_holds : OrthInnerCases := by
  intro F _ _ _ hF d _ Q hQ hT n hdn hn hV x hx L hL
  rcases OrthFix.orthInner_comp_cases hF hQ hT hdn hn hV x hx hL with
    ⟨hmem, hm, -, hLJ, -⟩ | ⟨_, -, -, -, -, -, i, hi, hiso⟩
  · exact Or.inl ⟨hmem, hm, hLJ⟩
  · exact Or.inr ⟨i, fixedIdx_of_orthFixedIdx hi, hiso⟩

theorem orthBlockFrame_holds : OrthBlockFrame := by
  intro Y _ _ K B J hB hBK _ F _ _ _ hF d hd Q hQ hT hker e hE x hx3 hmem hm3 hmq hJx a haB hat
  exact OrthFix.blockFrame_of_mem_E hB hBK hF hd hQ hT hker e hE x hx3 hmem hm3 hmq hJx
    (OrthFix.uniAut_fix_of_eq_conj hB hBK hd hQ hT e haB hat)

end OrthFC

section Closed

set_option linter.unusedSectionVars false

theorem bal207Open_of_leaves (hTor : OrthFix.OrthSU38ToralInput) (hBF : OrthFC.OrthBlockFrame)
    (hTri : D42TrialityShape) :
    SU38FrameOrth NonSemilinD4Eight ∧ SU38FrameD4 NonSemilinD4Eight ∧
      Bal207PlusFamOrth NonSemilinD4Eight ∧ Bal207PlusFamD4Eight NonSemilinD4Eight := by
  have hGA : GriessAllModelsStatement :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  refine ⟨OrthFix.su38FrameOrth_of_torus hTor OrthFix.uniAut_fix_of_eq_conj hGA _,
    su38FrameD4_of_torus hTor OrthFix.uniAut_fix_of_eq_conj hGA, ?_,
    bal207PlusFamD4Eight_of_griess hGA⟩
  exact OrthFix.bal207PlusFamOrth_of_inputs hGA OrthFix.orthInnerShapeInput_holds
    OrthFix.orthInnerUniqueTwo_holds hTri OrthFix.orthD4EightComp_holds
    (OrthFC.bal207OrthFirstClaim_of_innerCases hGA OrthFC.orthInnerCases_holds hBF _)

theorem bal207Corr_of_leaves (hTor : OrthFix.OrthSU38ToralInput) (hBF : OrthFC.OrthBlockFrame)
    (hTri : D42TrialityShape) : Bal207Corr :=
  have h := bal207Open_of_leaves hTor hBF hTri
  bal207Corr_of_open h.1 h.2.1 h.2.2.1 h.2.2.2

theorem bal207D4_of_leaves (hTor : OrthFix.OrthSU38ToralInput) (hBF : OrthFC.OrthBlockFrame)
    (hTri : D42TrialityShape) : OuterFourAux.Bal207D4 IsGraphAutFour :=
  have h := bal207Open_of_leaves hTor hBF hTri
  bal207D4_isGraphAutFour_of_open h.1 h.2.1 h.2.2.1 h.2.2.2

theorem bal207Corr_of_triality (hTri : D42TrialityShape) : Bal207Corr :=
  bal207Corr_of_leaves OrthFix.orthSU38ToralInput_holds OrthFC.orthBlockFrame_holds hTri

theorem bal207D4_of_triality (hTri : D42TrialityShape) : OuterFourAux.Bal207D4 IsGraphAutFour :=
  bal207D4_of_leaves OrthFix.orthSU38ToralInput_holds OrthFC.orthBlockFrame_holds hTri

end Closed

end CFSG.HardMathSupport.Dickson.Bal207

end
