
module

public import CFSG.GF2Type.Smith1979.GammaU.ResidualPairInputs
public import CFSG.GF2Type.Smith1979.GammaU.Violation

@[expose] public section

namespace CFSG.GF2Type.Smith1979.GammaU.ResPair

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol

@[expose] def n2 (i : ℕ) : Subgroup (V12 ≃ₗ[ZMod 2] V12) := genGrp (n2Gens i)

end CFSG.GF2Type.Smith1979.GammaU.ResPair
