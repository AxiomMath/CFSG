module

public import CFSG.Assembly.Defs
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Sporadic.Schreier.Enumeration
public import CFSG.Sporadic.Schreier.M23Gens

public section

namespace CFSG.QuasithinUnique.DoubleA3.K32Mathieu

open CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier

@[expose] def m23Rep3Words : List (List ℤ) :=
  [[1, 2, 2, 1, 2, 2]]

@[expose] def m23Rep3 : List (Equiv.Perm (Fin 23)) :=
  m23Rep3Words.map (evalCodes [m23PermA, m23PermB])

@[expose] def m23Cent3Words : List (List ℤ) :=
  [[-1, 2, 2],
   [-2, -1, -2, -2, -1, -2, -2, -2, -1, -2, -1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2],
   [-1, -2, -1, -2, -2, -2, -1, -2, -2, -1, -2, -1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2]]

@[expose] def m23Cent3ChainWords : List (List ℤ) :=
  [[-1, 3, 1]]

@[expose] def m23Cent3Q : RawSchreierDatum 23 :=
  certificate (by decide) (m23Cent3Words.map (evalCodes [m23PermA, m23PermB])) m23Cent3ChainWords
    #v[0, 2] (by decide)

@[expose] def m22Rep3Words : List (List ℤ) :=
  [[1, 2, 1, 2, 1, -2, 1, -2]]

@[expose] def m22Rep3 : List (Equiv.Perm (Fin 22)) :=
  m22Rep3Words.map (evalCodes [m22gA, m22gB])

@[expose] def m22Cent3Words : List (List ℤ) :=
  [[-1, -2, -2, -2, -1, -2, -2, -2, 1, 2, 2, 2, 1, 2, 2, 2],
   [-2, -1, -2, -2, -1, -2, -1, 2, 2, 1, 2, 1, 2, 2, 1, 2],
   [-1, -2, -1, -2, -2, -1, -2, -1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1],
   [-1, -2, -1, -2, -2, -2, -1, -2, -1, -2, -1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2]]

@[expose] def m22Cent3ChainWords : List (List ℤ) :=
  [[-4, -1]]

@[expose] def m22Cent3Q : RawSchreierDatum 22 :=
  certificate (by decide) (m22Cent3Words.map (evalCodes [m22gA, m22gB])) m22Cent3ChainWords
    #v[0, 1] (by decide)

end CFSG.QuasithinUnique.DoubleA3.K32Mathieu
