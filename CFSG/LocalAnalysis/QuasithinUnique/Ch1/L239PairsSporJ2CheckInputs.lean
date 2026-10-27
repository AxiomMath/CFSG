module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ2Data
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ2Defs

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.J2Pairs
open scoped Pointwise
open CFSG.Sporadic.Schreier

@[expose] def s0gen : List XJ := s0Words.map genX

@[expose] def S0X : List XJ := closureListH tabX hkey s0gen 40

@[expose] def A1X : List XJ :=
  S0X.filter fun x => s0gen.all fun s => enc (s * x) == enc (x * s)

@[expose] def Z2X : List XJ :=
  S0X.filter fun y => s0gen.all fun s => (A1X.map enc).contains (enc (y * s * y⁻¹ * s⁻¹))

@[expose] def A2X : List XJ := S0X.filter fun x => Z2X.all fun y => enc (y * x) == enc (x * y)

@[expose] def a2gen : List XJ := a2Words.map (evalW s0gen)

@[expose] def A2cl : List XJ := closureListH tabX hkey a2gen 40

@[expose] def t1X : XJ := genX t1Word

@[expose] def k1gen : List XJ := s0gen ++ [t1X]

@[expose] def K1X : List XJ := closureListH tabX hkey k1gen 40

@[expose] def gensA : List XJ := [paC, pbC]

@[expose] def F1X : Finset (Fin 315) := fixSetL A1X

@[expose] def orb1 : List (Finset (Fin 315)) × List ℕ × List ℕ := bfsOrbit id maskF gensA F1X 1000

@[expose] def t2X : XJ := genX t2Word

@[expose] def k2gen : List XJ := s0gen ++ [t2X]

@[expose] def K2X : List XJ := closureListH tabX hkey k2gen 40

@[expose] def F2X : Finset (Fin 315) := fixSetL A2X

@[expose] def orb2 : List (Finset (Fin 315)) × List ℕ × List ℕ := bfsOrbit id maskF gensA F2X 1000

@[expose] def q1gen : List XJ := q1Words.map (evalW s0gen)

@[expose] def Q1X : List XJ := closureListH tabX hkey q1gen 40

@[expose] def jLetters : List XJ := s0gen ++ [t1X, t2X]

end CFSG.QuasithinUnique.Vol2Native.L239.J2Pairs
