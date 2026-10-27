module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.E78
public import CFSG.LieType.SeitzGeneration.ExcHighThree.E6Reduction

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.LieType.SeitzGeneration TauCeti

section Assembly

theorem seitzExcHighForAt_top_three_of_open
    (hNR4 : LangPlaneKillsRoot .F4) (hPS : F4PureSplit) (hPT : F4PureTwisted)
    (hS1 : F4RegularSolvable 1) (hS2 : F4RegularSolvable 2) (hTwo : F4ThreeTwo)
    (hE6a : E6HighInF4 1) (hE6b : E6HighInF4 2) (hTwa : TwE6HighInF4 1) (hTwb : TwE6HighInF4 2)
    (hNR7 : LangPlaneKillsRoot .E7) (hK7 : LangPlaneKilled .E7)
    (hNR8 : LangPlaneKillsRoot .E8) (hK8 : LangPlaneKilled .E8) :
    SeitzExcHighForAt IsTopIndex PrimeRange.three := by
  have htor : LangToralOrParabolic .F4 :=
    langToralOrParabolic_of_langToralPlane
      CFSG.HardMathSupport.Timmesfeld.Torality.langToralPlane_F4_three
  have hF1 : F4ThreeNative 1 :=
    f4ThreeNative_of_pilot (Or.inl rfl) htor hNR4 (f4RegularPure_one_of_pure hPS) hS1
      (fun h => absurd h (by decide))
  have hF2 : F4ThreeNative 2 :=
    f4ThreeNative_of_pilot (Or.inr rfl) htor hNR4 (f4RegularPure_two_of_pure hPT) hS2
      (fun _ => hTwo)
  exact seitzExcHighForAt_top_three_of_cases (seitzExcHighThreeF4_of_native hF1)
    (seitzExcHighThreeF4_of_native hF2)
    (seitzExcHighThreeE6_of_native (e6ThreeNative_of_F4 hF1 hE6a))
    (seitzExcHighThreeE6_of_native (e6ThreeNative_of_F4 hF2 hE6b))
    (seitzExcHighThreeE7_of_pieces hNR7 hK7) (seitzExcHighThreeE8_of_pieces hNR8 hK8)
    (seitzExcHighThreeTwE6_of_native (twE6ThreeNative_of_F4 hF1 hTwa))
    (seitzExcHighThreeTwE6_of_native (twE6ThreeNative_of_F4 hF2 hTwb))

end Assembly

end CFSG.LieType.SeitzGeneration.ExcHighThree
