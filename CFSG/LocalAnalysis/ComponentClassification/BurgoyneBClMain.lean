module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBClPSLMain
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBClPSUMain
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBClSpMain

public section

namespace CFSG.ComponentClassification.Burgoyne

theorem burgoynePropBClassicalS_holds : BurgoynePropBClassicalS := by
  intro S _ _ τ n p f hτ hp2 hL v hv R hRH hRc p₁ n₁ _ hp₁2 hn₁ N _ hN hiso
  have key : Cl.NoL2At v := by
    rcases hτ with ⟨hτ, hn6, -⟩ | ⟨rfl, hn3⟩
    · rcases hτ with rfl | rfl
      · exact Cl.noL2At_of_lieModel_PSL hp2 hn6 hL hv
      · exact Cl.noL2At_of_lieModel_PSU hp2 hn6 hL hv
    · exact Cl.noL2At_of_lieModel_PSp hp2 hn3 hL hv
  exact key R hRH hRc p₁ n₁ hp₁2 hn₁ N hN hiso

end CFSG.ComponentClassification.Burgoyne
