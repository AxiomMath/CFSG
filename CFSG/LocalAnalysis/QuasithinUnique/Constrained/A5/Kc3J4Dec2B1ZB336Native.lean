module

public import CFSG.Sporadic.J4.QT2ANative

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT2A

@[expose] def zB336Word : List Int :=
  w5 "cAAccAccABCccBBCccBBCccBBCccBBCccBccAccAAbcBAbcBAbcBAbcBAbcBAbcBAbcBaaC"

@[expose] def zB336T0 (e : Nat) : Array V2 := mulRows (etaE e) (wR zB336Word)

@[expose] def zGwB336a : List Int := [-3, -2, -1, -3, 5, 4, 5, 5, 5, 1, 1, 2, 1, 2, 3, 2, 2, 3]

@[expose] def zGwB336b : List Int :=
  [-1, -2, -3, -2, -2, 5, 4, 5, 5, 5, 1, 3, 1, 3, 3, 3, 3, 3, 3, 1]

@[expose] def zGwB336c : List Int := [-1, -1, -2, -1, -3, 5, 4, 5, 5, 5, 2, 1, 1, 2, 2, 3, 3, 1]

@[expose] def zGwB336d : List Int := [-3, -2, -1, 5, 4, 5, 5, 5, 1, 2, 2, 3, 1, 3, 1, 2, 3, 2]

end CFSG.QuasithinUnique.A5
