module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.FourCheck
public import CFSG.Sporadic.Schreier.MathieuOddCoreM11Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rank

public section

namespace CFSG.EvenSporadicStandard.M11Std

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.EvenSporadicStandard.HypOne

@[expose] def gens : List (Equiv.Perm (Fin 11)) := [m11gA, m11gB]

@[expose] def centGens1 : List (Equiv.Perm (Fin 11)) := m11CentWords1.map (evalCodes gens)

@[expose] def fourWords1 : List (List ℤ) := [[1, 3]]

@[expose] def fourData : Bool := fourCheck 11 m11CentQ1 centGens1 fourWords1 400

end CFSG.EvenSporadicStandard.M11Std
