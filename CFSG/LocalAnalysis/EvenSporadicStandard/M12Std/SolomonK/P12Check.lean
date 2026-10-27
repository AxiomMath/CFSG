module

public section

namespace CFSG.EvenSporadicStandard.M12Std.SolomonK.P12

@[expose] def pid (n : Nat) : Array Nat := Array.ofFn (n := n) fun i => i.val

@[expose] def pmul (n : Nat) (P Q : Array Nat) : Array Nat :=
  Array.ofFn (n := n) fun i => P[Q[i.val]!]!

@[expose] def pswap (n a b : Nat) : Array Nat :=
  Array.ofFn (n := n) fun i => if i.val = a then b else if i.val = b then a else i.val

@[expose] def swapsArr (n : Nat) (w : List (Nat × Nat)) : Array Nat :=
  w.foldr (fun ab acc => pmul n (pswap n ab.1 ab.2) acc) (pid n)

@[expose] def wordArr (n : Nat) (G : List (Array Nat)) (w : List Nat) : Array Nat :=
  w.foldr (fun l acc => pmul n (G.getD l #[]) acc) (pid n)

@[expose] def allDistinct : List (Array Nat) → Bool
  | [] => true
  | x :: xs => !xs.contains x && allDistinct xs

@[expose] def commB (n : Nat) (x y : Array Nat) : Bool := pmul n x y == pmul n y x

@[expose] def sqB (n : Nat) (x : Array Nat) : Bool := pmul n x x == pid n

@[expose] def swapsOK (n : Nat) (w : List (Nat × Nat)) : Bool :=
  w.length % 2 == 0 && w.all fun ab => ab.1 < n && ab.2 < n && ab.1 != ab.2

@[expose] def enumOK (n : Nat) (G : List (Array Nat)) (L : List (List Nat)) : Bool :=
  let vals := L.map (wordArr n G)
  L.all (fun w => w.all (· < G.length)) && L.contains [] &&
    (List.range G.length).all
      (fun k => vals.all fun v => vals.contains (pmul n v (G.getD k #[]))) &&
    allDistinct vals

@[expose] def elemAbOK (n : Nat) (EG : List (Array Nat)) : Bool :=
  EG.all (sqB n) && EG.all fun x => EG.all fun y => commB n x y

@[expose] def triple (n : Nat) (Cx : List (Array Nat)) : List (Array Nat) :=
  Cx.filter fun y => sqB n y && 64 ≤ (Cx.filter (commB n y)).length

@[expose] def countAt (n : Nat) (PV : List (Array Nat)) (x : Array Nat) : Bool :=
  (triple n (PV.filter (commB n x))).length < 64

@[expose] def countOK (n : Nat) (PV EV : List (Array Nat)) : Bool :=
  PV.all fun x => x == pid n || !sqB n x || EV.contains x || countAt n PV x

@[expose] def order8OK (n : Nat) (G : List (Array Nat)) (w : List Nat) : Bool :=
  let g := wordArr n G w
  let g2 := pmul n g g
  let g4 := pmul n g2 g2
  let g8 := pmul n g4 g4
  w.all (· < G.length) && g4 != pid n && g8 == pid n

@[expose] def normOK (n : Nat) (EV EG : List (Array Nat)) (c : Array Nat) : Bool :=
  pmul n c (pmul n c c) == pid n &&
    EG.all fun u => EV.contains (pmul n (pmul n c u) (pmul n c c))

@[expose] def pGenSw : List (List (Nat × Nat)) :=
  [[(0, 1), (1, 2), (2, 3), (8, 10)], [(0, 2), (8, 10)], [(0, 4), (1, 5), (2, 6), (3, 7)],
    [(4, 6), (8, 9), (9, 10), (10, 11)]]

@[expose] def eGenSw : List (List (Nat × Nat)) :=
  [[(0, 1), (2, 3)], [(0, 2), (1, 3)], [(4, 5), (6, 7)], [(4, 6), (5, 7)], [(8, 9), (10, 11)],
    [(8, 10), (9, 11)]]

@[expose] def cGenSw : List (List (Nat × Nat)) := [[(0, 1), (1, 2)], [(4, 5), (5, 6)]]

@[expose] def gWord : List Nat := [0, 2]

def wordsOf (n : Nat) (G : List (Array Nat)) : List (List Nat) :=
  let rec go : Nat → Nat → Array (Array Nat × List Nat) → Array (Array Nat × List Nat)
    | 0, _, acc => acc
    | fuel + 1, i, acc =>
      if h : i < acc.size then
        let x := acc[i].1
        let w := acc[i].2
        let acc' := (List.range G.length).foldl (fun acc k =>
          let y := pmul n x (G.getD k #[])
          if acc.any (fun e => e.1 == y) then acc else acc.push (y, w ++ [k])) acc
        go fuel (i + 1) acc'
      else acc
  (go 2000 0 #[(pid n, [])]).toList.map (·.2)

@[expose] def p12Check (n : Nat) (_ : Unit := ()) : Bool :=
  let PG := pGenSw.map (swapsArr n)
  let EG := eGenSw.map (swapsArr n)
  let CG := cGenSw.map (swapsArr n)
  let PW := wordsOf n PG
  let EW := wordsOf n EG
  let CW := wordsOf n CG
  let PV := PW.map (wordArr n PG)
  let EV := EW.map (wordArr n EG)
  pGenSw.all (swapsOK n) && eGenSw.all (swapsOK n) && cGenSw.all (swapsOK n) &&
    enumOK n PG PW && PW.length == 512 && enumOK n EG EW && EW.length == 64 &&
    enumOK n CG CW && CW.length == 9 && elemAbOK n EG && EG.all (PV.contains ·) &&
    order8OK n PG gWord && countOK n PV EV && CG.all (normOK n EV EG)

end CFSG.EvenSporadicStandard.M12Std.SolomonK.P12
