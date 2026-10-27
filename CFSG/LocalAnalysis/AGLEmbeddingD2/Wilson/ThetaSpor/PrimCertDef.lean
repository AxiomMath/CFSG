module

public section

namespace CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.PrimCert

@[expose] def evalW (L : Array (Array Nat)) (w : List Nat) (x : Nat) : Nat :=
  w.foldl (fun p l => (L[l]!)[p]!) x

@[expose] def grow (L : Array (Array Nat)) (q : Nat) :
    List Nat → List (List Nat) → Option (List Nat)
  | r, [] => some r
  | r, w :: ws =>
    if evalW L w 0 ∈ r ∧ evalW L w q ∉ r then grow L q (evalW L w q :: r) ws
    else if evalW L w q ∈ r ∧ evalW L w 0 ∉ r then grow L q (evalW L w 0 :: r) ws
    else none

@[expose] def wordsOK (L : Array (Array Nat)) (ws : List (List Nat)) : Bool :=
  ws.all fun w => w.all fun l => decide (l < L.size)

@[expose] def primOK (n : Nat) (L : Array (Array Nat)) (tw : List (List Nat))
    (ew : List (List (List Nat))) : Bool :=
  wordsOK L tw && wordsOK L ew.flatten &&
    (List.range n).all (fun q => evalW L (tw.getD q []) 0 == q) &&
    (List.range n).all fun q => q == 0 ||
      match grow L q [0] (ew.getD q []) with
      | none => false
      | some r => (List.range n).all fun p => decide (p ∈ r)

@[expose] def fourOK (n : Nat) (L : Array (Array Nat)) (w : List Nat) : Bool :=
  wordsOK L [w] && (List.range n).all (fun x => evalW L (w ++ w ++ (w ++ w)) x == x) &&
    (List.range n).any fun x => evalW L (w ++ w) x != x

end CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.PrimCert

end
