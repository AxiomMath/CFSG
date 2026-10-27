module

public import CFSG.GF2Type.Smith1979.GammaU.Step5
public import CFSG.GF2Type.Smith1979.GammaU.Frame

public section

namespace CFSG.GF2Type.Smith1979.GammaU.StepA

theorem frameCensus_holds
    {i : ℕ} (hi : i = 0 ∨ i = 1) : FrameCensus i :=
  fun H => FrameC.frameCensus hi H

theorem residualPairs_holds {i : ℕ} (hi : i = 0 ∨ i = 1) :
    ResidualPairs i :=
  fun _ hc hc1 => ResPair.residualPair hi hc hc1

end CFSG.GF2Type.Smith1979.GammaU.StepA
