module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21Sp44B
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21Sp44

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.EvenSporadicStandard.M24Std

theorem prop21Sp44Case :
    Prop21Sp44Case := by
  intro V _ hcomm hsq hcard G _ _ ρ hρ z hz hC hS
  have hG : Nat.card G ∣ gl8 := card_dvd_gl8 hcomm hsq hcard ρ hρ
  obtain ⟨hL, hzU⟩ := prop21_sp44_partial hz hC hG hS
  refine ⟨hL, hzU, ?_⟩
  obtain ⟨c⟩ := hC
  have := egaLayer_normal G
  exact sp44_clause3 hG c (egaLayer G) hL hzU

theorem fin77aProp21K_of_harrisSolomonK_of_a6a6
    (hHS : HarrisSolomonZ2S6IsoK) (hA6A6 : Prop21A6A6Case) : Fin77aProp21K :=
  fin77aProp21K_of_harrisSolomonK_of_cases hHS hA6A6 prop21Sp44Case

end CFSG.EvenSporadicStandard.M22Std
