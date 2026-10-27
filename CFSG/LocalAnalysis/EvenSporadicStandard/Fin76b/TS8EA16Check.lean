module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8D8Check

public section

namespace CFSG.EvenSporadicStandard.Fin76b.TS8EA16

open CFSG.EvenSporadicStandard.Fin76b.TS8D8

@[expose] def invsIx (M : Array (Array ℕ)) : List ℕ :=
  (List.range 256).filter fun a => a != 0 && mulIx M a a == 0

@[expose] def spanIx (M : Array (Array ℕ)) (S : List ℕ) (X : ℕ) : List ℕ :=
  S ++ S.map fun Y => mulIx M Y X

@[expose] def hasChainIx (M : Array (Array ℕ)) : ℕ → List ℕ → List ℕ → Bool
  | 0, _, _ => true
  | k + 1, S, C => C.tails.any fun T => match T with
    | [] => false
    | X :: T' => !decide (X ∈ S) && hasChainIx M k (spanIx M S X) (T'.filter fun Y => commIx M X Y)

@[expose] def chainFreeCheck (n : ℕ) (A B U : Array ℕ) (ws : List (List ℕ)) : Bool :=
  let M := mulTabT n (bfsT n (gensT n A B U ws)).1 (idxT (bfsT n (gensT n A B U ws)).1)
  !hasChainIx M 5 [0] (invsIx M)

@[expose] def checkEA16 (n : ℕ) (A B U : Array ℕ) (ws : List (List ℕ)) : Bool :=
  checkD8 n A B U ws && chainFreeCheck n A B U ws

end CFSG.EvenSporadicStandard.Fin76b.TS8EA16
