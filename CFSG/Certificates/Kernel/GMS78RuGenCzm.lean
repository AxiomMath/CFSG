module

public import CFSG.Certificates.Kernel.GMS78RuGenN
public import Certificates.Data.GMS78RuCzMatchCheck

public section

namespace CFSG.KC.GMS.Gen

open CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuN CFSG.ComponentClassification.GMS78.RuCz

section Czm

variable (nbt ntw : List (List (Fin 8))) (nc nb : List Nat) (img imgInv : List NTrip)

@[expose] def czmConjG (g gi x : NTrip) : NTrip := nMulT nbt ntw nc nb (nMulT nbt ntw nc nb g x) gi

@[expose] def czmSameG (y y' : NTrip) : Bool := y == y' || y == nMulT nbt ntw nc nb y' czmZ0

@[expose] def czmConjWG (w : List (Fin 7 × Bool)) (x : NTrip) : NTrip :=
  czmConjG nbt ntw nc nb (nEvalW nbt ntw nc nb img imgInv w)
    (nEvalW nbt ntw nc nb img imgInv (FreeGroup.invRev w)) x

@[expose] def czmZ0CheckG (z0w : List (Fin 7 × Bool)) : Bool :=
  nEvalW nbt ntw nc nb img imgInv z0w == czmZ0

@[expose] def czmLetterCheckG : Bool :=
  (List.range 5).all fun i =>
    nMulT nbt ntw nc nb (img.getD i nOneT) czmZ0 == nMulT nbt ntw nc nb czmZ0 (img.getD i nOneT) &&
    czmX0.all fun x => czmInX0 (czmConjG nbt ntw nc nb (img.getD i nOneT) (imgInv.getD i nOneT) x) &&
      czmInX0 (czmConjG nbt ntw nc nb (imgInv.getD i nOneT) (img.getD i nOneT) x)

@[expose] def czmJCheckG (jw : ℕ → List (Fin 7 × Bool)) : Bool :=
  (List.range 6).all fun i => czmX0.all fun x =>
    czmSameG nbt ntw nc nb (czmConjWG nbt ntw nc nb img imgInv (jw i) x) x

@[expose] def czmRepCheckG (rep : ℕ → List (Fin 7 × Bool)) : Bool :=
  (List.range 24).all fun i => (List.range 24).all fun j =>
    !decide (i < j) || czmX0.any fun x =>
      !czmSameG nbt ntw nc nb (czmConjWG nbt ntw nc nb img imgInv (rep i) x)
        (czmConjWG nbt ntw nc nb img imgInv (rep j) x)

end Czm

@[expose] def czmInvolCheckG (gl : List Lin8) : Bool :=
  gl.all fun r => !(linComp r r == linId && r != linId) ||
    decide (9 ≤ (gl.map fun c => czmConjCode c r).dedup.length)

end CFSG.KC.GMS.Gen

end
