module

public import CFSG.Certificates.Kernel.O8ChainDefs
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainT0Data

public section

namespace CFSG.KC.O8

open CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.EvenSmallLie.OmegaEight
  CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Chain CFSG.KLie.CT

@[expose] def liftTabG (G C : ℕ → Array ℕ) (W : Array (List ℕ)) : Array (Array (Array ℕ)) :=
  Array.ofFn (n := 64) fun i => prod4G G C (W.getD i [])

@[expose] def wordsCheckG (G : ℕ → Array ℕ) (S : Array (Array ℕ)) (W : Array (List ℕ)) : Bool :=
  (List.range 64).all fun i => wordRowsG G (W.getD i []) == s0GetG S i

@[expose] def uIdxCheckG (S : Array (Array ℕ)) (U : ℕ → Array ℕ) : Bool :=
  s0GetG S 4 == U 3 && s0GetG S 5 == U 4 && s0GetG S 6 == U 5

@[expose] def e0CheckG (S : Array (Array ℕ)) : Bool :=
  (List.range 64).all fun i => bmulVec 6 6 (s0GetG S i) 1 == 1

@[expose] def t0CheckG (S : Array (Array ℕ)) (LT : Array (Array (Array ℕ))) : Bool :=
  let T := mulTabG S
  (List.range 64).all fun q => [false, true].all fun e => (List.range 64).all fun s =>
    let x := tmul T LT (dig4 1, false, 0) (twoV q, e, s)
    t0Gens.any fun y => !(tmul T LT x y == tmul T LT y x)

@[expose] def commCheckG (S : Array (Array ℕ)) (LT : Array (Array (Array ℕ))) : Bool :=
  let T := mulTabG S
  (List.range 64).all fun q => [false, true].all fun e => (List.range 64).all fun s =>
    let l := tmul T LT (dig4 641, false, 0) (twoV q, e, s)
    let r := tmul T LT (twoV q, e, s) (dig4 641, false, 0)
    l == r || l == tmul T LT r (twoV 1, false, 0)

end CFSG.KC.O8

end
