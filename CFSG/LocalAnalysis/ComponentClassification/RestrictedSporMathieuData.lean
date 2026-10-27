module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM22OuterData
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23Data
public import CFSG.Sporadic.Schreier.MathieuOddCoreM24Data

public section

namespace CFSG.ComponentClassification.RestrictedStd.Spor

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Certificates

@[expose] def m23KGens : List (Equiv.Perm (Fin 23)) :=
  m23CentWords1.map (evalCodes [m23PermA, m23PermB])

@[expose] def m24K1Gens : List (Equiv.Perm (Fin 24)) := m24CentWords1.map (evalCodes [m24gA, m24gB])

@[expose] def m24K2Gens : List (Equiv.Perm (Fin 24)) := m24CentWords2.map (evalCodes [m24gA, m24gB])

@[expose] def m22OKGens : List (Equiv.Perm (Fin 22)) :=
  m22OutCentWords2.map (evalCodes [m22gA, m22gB])

end CFSG.ComponentClassification.RestrictedStd.Spor
