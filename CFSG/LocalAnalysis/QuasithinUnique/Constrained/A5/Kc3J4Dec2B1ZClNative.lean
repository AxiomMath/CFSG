module

public import CFSG.Sporadic.J4.QT2ANative

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT2A

@[expose] def zRowsOf (Rw : Nat → Array V2) (q : Nat × Nat) : Array V2 :=
  mulRows (etaE q.2) (Rw q.1)

@[expose] def zRowsComm (ms : Fin 4 → Array V2) (X : Array V2) : Bool :=
  (List.finRange 4).all fun i => eqRows (mulRows X (ms i)) (mulRows (ms i) X)

@[expose] def zPairOK (ms : Fin 4 → Array V2) (Rw : Nat → Array V2) (j c : Nat) : Bool :=
  zRowsComm ms (zRowsOf Rw (j, c))

@[expose] def zI (ms : Fin 4 → Array V2) (Rw : Nat → Array V2) (taus : List Nat) :
    List (Nat × Nat) :=
  taus.flatMap fun j => (List.range 2048).filterMap fun c =>
    if zPairOK ms Rw j c then some (j, c) else none

end CFSG.QuasithinUnique.A5
