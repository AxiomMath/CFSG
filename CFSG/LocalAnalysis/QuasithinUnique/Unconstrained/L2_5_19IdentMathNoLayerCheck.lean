module

public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore

public section

namespace CFSG.QuasithinUnique.Id2519.MathNoLayer

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native

@[expose] def memT (n : Nat) (x : Table) (L : List Table) : Bool := L.any fun y => tblEq n x y

@[expose] def noLayerOK (n : Nat) (E K : List Table) : Bool :=
  memT n (idT n) E &&
  E.all (fun e => memT n e K) &&
  E.all (fun e => let ei := invT n e; invOK n e ei && memT n ei E &&
    E.all fun f => memT n (compT n e f) E) &&
  K.all (fun q => let qi := invT n q; invOK n q qi &&
    E.all fun e => memT n (compT n (compT n q e) qi) E) &&
  K.all (fun q => !(E.all fun e => commT n q e) || memT n q E) &&
  E.all (fun e => tblEq n (powT n 4 e) (idT n))

end CFSG.QuasithinUnique.Id2519.MathNoLayer
