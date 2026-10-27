module

public import CFSG.HardMathSupport.Curtis.Coordinator.ExcLeafDefs
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityThreeRank

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.HardMathSupport.Foote.E27 CFSG.HardMathSupport.Curtis.Proving
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.SeitzGeneration TauCeti
open CFSG.HardMathSupport.Curtis.Coordinator.ExcLeaf (IdxTrialityD4)


section Certs


theorem innerLeaf_trialityD4 : InnerLeaf IdxTrialityD4 := by
  intro X _ _ K R T z h hz d hd e
  obtain ⟨i, hv⟩ := d
  obtain ⟨q, hq, rfl⟩ := hd
  obtain ⟨e⟩ := e
  exact false_of_E27_rankLE2 h hz
    (RankLE2.of_injective e.toMonoidHom e.injective (rankLE2_three_cat_trialityD4 q hv hq))

end Certs

end CFSG.HardMathSupport.Malle.E27Lie
