module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainZ4Data

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open CFSG.EvenSmallLie.UnitarySix.YamadaPar Stage1

@[expose] def s0Words : Array (List ℕ) :=
  #[[], [4, 2, 5, 3, 4, 2, 0, 1], [3, 2, 4, 5, 3, 2, 0, 1, 1, 0], [3, 4, 1, 0, 2, 5, 1, 0],
    [4, 2, 5, 3, 4, 2, 1, 0], [3, 2, 5, 4, 3, 2, 0, 1, 1, 0], [3, 5, 1, 0, 2, 4, 1, 0],
    [3, 2, 5, 4, 3, 2, 1, 0], [2, 5, 0, 1, 4, 3, 1, 0], [0, 1, 1, 0],
    [3, 2, 4, 5, 3, 2, 1, 0], [2, 4, 0, 1, 5, 3, 1, 0], [4, 3, 1, 0, 5, 2, 1, 0],
    [3, 2, 5, 4, 3, 2, 0, 1], [4, 2, 5, 3, 4, 2], [4, 2, 1, 0, 5, 3],
    [5, 2, 0, 1, 3, 4, 1, 0], [2, 5, 1, 0, 3, 4, 1, 0], [4, 3, 1, 0, 5, 2],
    [4, 5, 5, 4, 0], [3, 2, 4, 5, 3, 2, 0, 1], [2, 4, 1, 0, 3, 5, 1, 0],
    [5, 2, 1, 0, 4, 3], [5, 3, 1, 0, 4, 2, 1, 0], [4, 2, 0, 1, 3, 5, 1, 0],
    [5, 3, 1, 0, 4, 2], [3, 2, 4, 5, 3, 2], [0, 1], [5, 3, 0, 1, 2, 4],
    [3, 4, 0, 1, 5, 2, 1, 0], [5, 2, 0, 1, 3, 4], [2, 2, 3, 0, 2, 1], [3, 2, 5, 4, 3, 2],
    [3, 5, 0, 1, 4, 2, 1, 0], [4, 3, 0, 1, 2, 5], [4, 2, 0, 1, 3, 5],
    [5, 2, 1, 0, 4, 3, 1, 0], [3, 4, 1, 0, 2, 5], [2, 5, 5, 3, 1, 4, 0, 2], [1, 0],
    [2, 5, 1, 0, 3, 4], [2, 4, 1, 0, 3, 5], [3, 5, 0, 1, 4, 2], [4, 3, 0, 1, 2, 5, 1, 0],
    [2, 5, 0, 1, 4, 3], [4, 2, 3, 4, 5, 1, 2], [2, 2, 3, 1, 2], [5, 2, 3, 5, 4, 0, 2, 1],
    [2, 1, 3, 0, 2], [4, 2, 3, 4, 5, 0, 2, 1], [4, 2, 1, 0, 5, 3, 1, 0],
    [5, 3, 0, 1, 2, 4, 1, 0], [3, 4, 0, 1, 5, 2], [2, 4, 4, 3, 1, 5, 0, 2],
    [3, 5, 1, 0, 2, 4], [2, 4, 0, 1, 5, 3], [5, 2, 3, 5, 4, 1, 2],
    [4, 2, 5, 3, 4, 2, 0, 1, 1, 0], [4, 1, 5, 0, 4], [2, 3, 4, 5, 3, 2, 0],
    [4, 4, 5, 1, 4], [2, 3, 5, 4, 3, 2, 0], [2, 3, 3, 2, 0], [4, 4, 5, 0, 4, 1]]

@[expose] def liftTab : Array (Array (Array ℕ)) :=
  Array.ofFn (n := 64) fun i => prod4 .plus (s0Words.getD i [])

@[expose] def addV4 (v w : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 6) fun j => (v.getD j 0 + w.getD j 0) % 4

@[expose] def negV4 (v : Array ℕ) : Array ℕ := Array.ofFn (n := 6) fun j => (3 * v.getD j 0) % 4

@[expose] def tmul (T : Array (Array ℕ)) (LT : Array (Array (Array ℕ)))
    (g h : Array ℕ × Bool × ℕ) : Array ℕ × Bool × ℕ :=
  let w := mv4 (LT.getD g.2.2 #[]) h.1
  (addV4 g.1 (if g.2.1 then negV4 w else w), g.2.1 ^^ h.2.1, tabGet T g.2.2 h.2.2)

@[expose] def twoV (q : ℕ) : Array ℕ := Array.ofFn (n := 6) fun j => if q.testBit j then 2 else 0

@[expose] def t0Gens : List (Array ℕ × Bool × ℕ) :=
  [(twoV 1, false, 0), (twoV 2, false, 0), (twoV 4, false, 0), (dig4 0, false, 4),
    (dig4 0, false, 5), (dig4 0, false, 6)]

@[expose] def wordsCheck : Bool :=
  (List.range 64).all fun i => wordRows .plus (s0Words.getD i []) == s0Get .plus i

@[expose] def uIdxCheck : Bool :=
  s0Get .plus 4 == uRows .plus 3 && s0Get .plus 5 == uRows .plus 4 &&
    s0Get .plus 6 == uRows .plus 5

@[expose] def e0Check : Bool := (List.range 64).all fun i => bmulVec 6 6 (s0Get .plus i) 1 == 1

@[expose] def t0Check : Bool :=
  let T := mulTab .plus
  let LT := liftTab
  (List.range 64).all fun q => [false, true].all fun e => (List.range 64).all fun s =>
    let x := tmul T LT (dig4 1, false, 0) (twoV q, e, s)
    t0Gens.any fun y => !(tmul T LT x y == tmul T LT y x)

end CFSG.EvenSmallLie.OmegaEight.Chain
