
module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Reps2B0
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2Gen

public section

namespace CFSG.QuasithinUnique.A5
open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A CFSG.Sporadic.J4.QT2 CFSG.QuasithinUnique.A5.Dec2

@[expose] def b1344P : List Int := (b1344Words.getD 0 []).take 25

@[expose] def b1344S : List Int := (b1344Words.getD 0 []).drop 199

@[expose] def b1344Q : Array V2 :=
  mulRows (mulRows (wR b1344P) (etaE 269)) (wR b1344S)

end CFSG.QuasithinUnique.A5
