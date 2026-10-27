module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabThCensusInputs
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporThKit
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenInputs
public meta import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabThCensusInputs
public meta import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporThKit
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenInputs

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabThNative

open CFSG.Sporadic.Th.Native CFSG.SectionRank.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpNative
  CFSG.RankThree.PartTwo.Sec4.Item434SporTh CFSG.Monster.B.Fischer
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThLocal
  CFSG.HardMathSupport.Dickson.Sec6.Up34Th.ThThreeNative

set_option compiler.extract_closed false

@[expose] def wordIdx (edges : Array (Array Nat)) (w : List Nat) : Nat :=
  w.foldr (fun l i => (edges[i]!)[l]!) 0

@[expose] def digits3 (k : Nat) : List Nat :=
  [k % 3, (k / 3) % 3, (k / 9) % 3, (k / 27) % 3, (k / 81) % 3]

@[expose] def prodIdx (mul : Nat → Nat → Nat) (rI : List Nat) (e : List Nat) : Nat :=
  (rI.zip e).foldl (fun acc p => mul acc (powIdx mul p.1 p.2)) 0

@[expose] def inArr (N : Nat) (S : List Nat) : Array Bool :=
  S.foldl (fun a i => a.set! i true) (Array.replicate N false)

@[expose] def uTableOK' (N : Nat) (mul : Nat → Nat → Nat) (g0 g1 gi0 gi1 : Nat) (rI S : List Nat)
    (inR : Array Bool) : Bool :=
  decide (rI.length = 5) && rI.all (fun r => powIdx mul r 3 == 0) &&
    rI.all (fun r => rI.all fun r' => mul r r' == mul r' r) &&
    decide (S.toFinset.card = 243) && S.all (fun a => decide (a < N)) &&
    S.all (fun a => powIdx mul a 3 == 0) && inR[0]! && rI.all (fun r => inR[r]!) &&
    S.all (fun a => S.all fun b => inR[mul a b]!) &&
    (powIdx mul g0 30 == 0) && (powIdx mul g1 30 == 0) &&
    (gi0 == powIdx mul g0 29) && (gi1 == powIdx mul g1 29) &&
    rI.all (fun r => inR[mul (mul g0 r) gi0]! && inR[mul (mul gi0 r) g0]! &&
      inR[mul (mul g1 r) gi1]! && inR[mul (mul gi1 r) g1]!) &&
    (List.range N).all fun i => !(rI.all fun r => mul i r == mul r i) || inR[i]!

@[expose] def uTableOK (N : Nat) (c : ArrCert) (rw : List (List Nat)) : Bool :=
  let mul := mulIdxN c.edges c.par c.lab N
  let rI := rw.map (wordIdx c.edges)
  let S : List Nat := (List.range 243).map fun k => prodIdx mul rI (digits3 k)
  decide (rw.length = 5) && rw.all (fun w => w.all fun l => decide (l < 2)) &&
    uTableOK' N mul ((c.edges[0]!)[0]!) ((c.edges[0]!)[1]!)
      (powIdx mul ((c.edges[0]!)[0]!) 29) (powIdx mul ((c.edges[0]!)[1]!) 29) rI S (inArr N S)

@[expose] def uGens (R : Array (Array V4)) : Array Mat := #[R[20]!, R[21]!]

@[expose] def thUCheck (rw : List (List Nat)) (v : Array Nat) (fuel N : Nat) : Bool :=
  let R := regsU ()
  let P : Array Mat := uGens R
  let tabs := tabsOf P
  let c := orbCert tabs v fuel
  commOK R[22]! R[20]! && commOK R[22]! R[21]! && orbitOK tabs v c N && uTableOK N c rw

@[expose] def uRWords : List (List Nat) := [
  [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0],
  [1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0],
  [0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1],
  [0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1],
  [1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1]]

@[expose] def uVec : Array Nat :=
  #[6658737767427314907, 16544147111678123163, 14163415142073636367, 43455227551927286]

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenNative in
@[expose] def thUScanOK (c : Nat) : Bool :=
  centCheckMulti ((regsU ())[22]!) 174960 c 0 10000

@[expose] def thUOK (_ : Unit := ()) : Bool := thUCheck uRWords uVec 175000 174960

end CFSG.HardMathSupport.Dickson.I271.TabThNative
