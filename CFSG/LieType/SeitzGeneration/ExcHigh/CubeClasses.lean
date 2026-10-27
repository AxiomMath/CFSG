module

public import CFSG.LieType.SeitzGeneration.ExcHigh.CubePlanes
public import CFSG.LieType.SeitzGeneration.ExcHigh.E6Low
public import CFSG.HardMathSupport.Malle.SeitzCube.E6ThreeProved
public import CFSG.HardMathSupport.Lang.TwE6Step3.CubesV4

public section

namespace CFSG.LieType.SeitzGeneration.ExcHigh


theorem seitzExcHighE6Three_proved : SeitzExcHighE6Three :=
  seitzExcHighE6Three_of_cube CFSG.HardMathSupport.Malle.SeitzCube.excCubeHighAt_E6_three_proved

theorem seitzExcHighE6_geFive_proved : SeitzExcHighForAt IsE6Index PrimeRange.geFive :=
  seitzExcHighE6_geFive_of_three seitzExcHighE6Three_proved

theorem seitzExcHighE7Six_proved : SeitzExcHighE7Six :=
  seitzExcHighE7Six_of_cube
    CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.excCubeHighAt_E7_six_proved

theorem seitzExcHighTwE6Six_of_phi6
    (h6 : ∀ r, 5 ≤ r → CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.PhiPlaneGenAt (-1) r) :
    SeitzExcHighTwE6Six :=
  seitzExcHighTwE6Six_of_cube
    (CFSG.HardMathSupport.Lang.TwE6Step3.excCubeResidualsV4_of_phi6 h6).twE6Six

end CFSG.LieType.SeitzGeneration.ExcHigh
