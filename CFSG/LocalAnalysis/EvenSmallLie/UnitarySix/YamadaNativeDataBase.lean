
module

public import CFSG.Sporadic.Schreier.Outer
public import Certificates.Data.CFSGNative.SporadicSchreier.Count

@[expose] public section

namespace CFSG.EvenSmallLie.UnitarySix.Yamada

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native

def orbitWords : List (List ℤ) :=
  [[], [1], [-1], [2, 1], [3, 1], [1, 2, 1], [3, 2, 1], [-1, 2, 1], [1, 3, 1], [-1, 3, 1],
    [2, 1, 2, 1], [3, 1, 2, 1], [1, 3, 2, 1], [-1, 3, 2, 1], [2, 1, 3, 1], [3, 1, 3, 1],
    [3, 2, 1, 2, 1], [1, 3, 1, 2, 1], [-1, 3, 1, 2, 1], [3, 1, 3, 2, 1], [3, -1, 3, 1, 2, 1]]

def stabWords : List (List ℤ) :=
  [[], [], [-1, 2, -1, 2, -1, 2, 1, 2, 1, 2], [2], [3], [2, -1, 2, 1, 2, -1, 2, 1], [2, 3],
    [-1, 2, -1, 2, -1, 2, 1, 2, 1], [3, -1, 3, 1, 3, -1, 3, 1], [-1, 3, -1, 3, -1, 3, 1, 3, 1],
    [-1, 2, 1, 2, -1, 2, 1], [2, 3, -1, 2, 1, 2, -1, 2, 1], [2, -1, 3, 1, 2, -1, 3, 1],
    [-1, 2, 3, -1, 2, -1, 3, 1, 2, 1], [2, 3, -1, 3, 1, 3, -1, 3, 1], [-1, 3, 1, 3, -1, 3, 1],
    [3, -1, 2, 1, 2, -1, 2, 1], [2, -1, 3, 1, 3, -1, 3, 1], [-1, 3, 1, 2, -1, 3, 1],
    [-1, 2, 1, 3, -1, 2, 1], [2, -1, 2, 1, 3, -1, 2, 1]]

end CFSG.EvenSmallLie.UnitarySix.Yamada
