module

public import CFSG.Literature.GL52Basic
public import CFSG.Sporadic.Schreier.CountSpec
public meta import CFSG.Literature.GL52Basic
public meta import CFSG.Sporadic.Schreier.CountSpec
public meta import Mathlib
public import Mathlib

public section

namespace CFSG.Literature.GL52

open Matrix CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native

instance : MulAction G (Fin 31) := MulAction.compHom _ glPerm

@[expose] def glA : G :=
  ⟨!![0, 0, 0, 0, 1; 1, 0, 0, 0, 0; 0, 1, 0, 0, 1; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0],
    !![0, 1, 0, 0, 0; 1, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1; 1, 0, 0, 0, 0],
    by decide, by decide⟩

@[expose] def glB : G :=
  ⟨!![1, 1, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
    !![1, 1, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
    by decide, by decide⟩

@[expose] def glWords : List (List ℤ) :=
  [[-1, -1, 2, 1, 1], [-1, 3, 1], [-1, 4, 1], [-1, 5, 1], [-1, -1, 6, 1, 1], [-1, 7, 1],
    [-6, -8, -1, -1, 8, 1, 1], [-5, -4, -3, 9, -6, -3, -5, -1, 9, 1], [-10, -10],
    [-5, -9, -7, -1, 10, 1], [-12, -12], [-4, -3, -10, -4, -1, 13, 1]]

@[expose] def glCert : RawSchreierDatum 31 :=
  certificate (by decide) [tab (glPerm glA), tab (glPerm glB)] glWords #v[0, 1, 3, 7, 15]
    (by decide)

end CFSG.Literature.GL52
