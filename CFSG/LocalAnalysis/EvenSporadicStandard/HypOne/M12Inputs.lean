module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Check
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12ModelData

public section

namespace CFSG.EvenSporadicStandard.HypOne.M12

open CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native

@[expose] def gens : List (Equiv.Perm (Fin 12)) := [m12gA, m12gB]

@[expose] def wordE1 : List ℤ :=
  [2, -1, 2, -1, -2, -1, -2, -2, -1, -2, -1, 2, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, -2, 1,
    2, 1, 2, 1, -2, -1, -2, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1,
    -2, -1, -2, -1, 2, -1, -2, -1, 2, -1, -2]

@[expose] def wordE2 : List ℤ :=
  [-1, -2, -1, 2, -1, 2, -1, -2, -1, 2, -1, -2, -1, 2, -1, -2, -1, -2, -1, 2, -1, 2, -1, 2, -1, -2,
    -1, 2, -1, -1, -2, -1, 2, -1, -2, -2, 1, -2, 1, -2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1,
    -2, 1, 2, 1, 2, 1, 2]

@[expose] def wordE3 : List ℤ :=
  [-1, -2, -1, 2, -1, 2, -1, -2, -1, -2, -1, -2, -1, -2, -2, -1, -2, -1, 2, 2, 1, 2, 1, 2, 1, 2, 1,
    -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, -1]

@[expose] def e1 : Equiv.Perm (Fin 12) := evalCodes gens wordE1

@[expose] def e2 : Equiv.Perm (Fin 12) := evalCodes gens wordE2

@[expose] def e3 : Equiv.Perm (Fin 12) := evalCodes gens wordE3

@[expose] def e8Data : Bool := e8Check 12 (toTable e1) (toTable e2) (toTable e3)

@[expose] def foursData : Bool :=
  ordTest 12 2 (toTable ((m12gB * m12gA * m12gB⁻¹) * (m12bp * m12gA * m12bp⁻¹)⁻¹))

end CFSG.EvenSporadicStandard.HypOne.M12
