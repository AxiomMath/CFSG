module

public import CFSG.HardMathSupport.Dickson.Bal207.D4GraphBridge
public import CFSG.HardMathSupport.Dickson.Bal207.Final

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourInAux

theorem isD4EightIdx_of_isD4EightIndex {d : TauCeti.LieTypeIndex}
    (h : OuterFourAux.IsD4EightIndex d) : IsD4EightIdx d := by
  cases d with
  | D r q => exact h
  | _ => exact h.elim

section Wrap

set_option linter.unusedSectionVars false


theorem bal207D4_isGraphAutFour_of_open (hFOrth : SU38FrameOrth NonSemilinD4Eight)
    (hFD4 : SU38FrameD4 NonSemilinD4Eight) (hOrth : Bal207PlusFamOrth NonSemilinD4Eight)
    (hD4 : Bal207PlusFamD4Eight NonSemilinD4Eight) :
    OuterFourAux.Bal207D4 IsGraphAutFour := by
  intro X _ _ hX K B hcomp hSC hBN hK hNT
  obtain ⟨d, hd, ⟨e⟩⟩ := hK
  have hd' : IsD4EightIdx d.1 := isD4EightIdx_of_isD4EightIndex hd
  refine bal207D4Eight_of_open hFOrth hFD4 hOrth hD4 X hX K B hcomp hSC hBN ⟨d, hd', ⟨e⟩⟩ ?_
  rintro φ hφ ⟨h3, hns⟩
  exact hNT φ hφ ⟨h3, graphAutD4_of_not_semilin_idx hd' e φ h3 hns⟩

end Wrap

end CFSG.HardMathSupport.Dickson.Bal207

end
