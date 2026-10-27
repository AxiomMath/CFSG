module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBaseNative

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.QuasithinUnique.K1.SporadicPerm

@[expose] def rowOf (P : List Nat) (Y : Array Nat) : List Nat := P.map (img Y)

@[expose] def commInR (nb : Nat) (Z : List (Array Nat)) (T : List Nat) (j : Nat) (s : Array Nat) :
    Bool :=
  Z.any fun Y => (List.range nb).all fun k =>
    T.getD (nb * (1 + j) + k) 0 == img Y (img s (T.getD k 0))

@[expose] def passAll (nb : Nat) (gens : List (Array Nat)) (Z : List (Array Nat)) (T : List Nat) :
    Bool :=
  (List.range gens.length).all fun j => commInR nb Z T j (gens.getD j #[])

@[expose] def zClaimOK (nb : Nat) (gens : List (Array Nat)) (P : List Nat)
    (Ts : Array (List Nat)) (Z L : List (Array Nat)) : Bool :=
  Ts.toList.all (fun T => passAll nb gens Z T == (L.map (rowOf P)).contains T) &&
    L.all fun Y => Ts.contains (rowOf P Y)

@[expose] def nodesLt (m : Nat) (l : List Nat) : Bool := l.all fun i => decide (i < m)

end CFSG.QuasithinUnique.Setup.X1
