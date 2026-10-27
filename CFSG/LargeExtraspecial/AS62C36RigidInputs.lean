module

public import CFSG.LargeExtraspecial.AS62Model
public import CFSG.LargeExtraspecial.AS62SemData2
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP0Base

public section

namespace CFSG.LargeExtraspecial.AS62.Rigid

open CFSG.Quasithin CFSG.Quasithin.H13.F431.U42Aut CFSG.LargeExtraspecial.AS62.Sem

@[expose] def cmpA (a b : Array Nat) : Array Nat := b.map fun j => a.getD j 0

@[expose] def idA : Array Nat := (List.range 45).toArray

@[expose] def evalA {α : Type} (L : α × Bool → Array Nat) (w : List (α × Bool)) : Array Nat :=
  w.foldr (fun a acc => cmpA (L a) acc) idA

@[expose] def invWord {α : Type} (w : List (α × Bool)) : List (α × Bool) :=
  (w.map fun a => (a.1, !a.2)).reverse

@[expose] def genA (k : Nat) : Array Nat := (uLists.getD k []).toArray

@[expose] def genInvA (k : Nat) : Array Nat := (uInvLists.getD k []).toArray

@[expose] def letA (c : Nat × Bool) : Array Nat := if c.2 then genA c.1 else genInvA c.1

@[expose] def bPair (k : Fin 192) : Array Nat × Array Nat :=
  (evalA (fun a : Fin 4 × Bool => letA (a.1.val, a.2)) (bWord k),
    evalA (fun a : Fin 4 × Bool => letA (a.1.val, a.2)) (invWord (bWord k)))

@[expose] def bTab (_ : Unit := ()) : Array (Array Nat × Array Nat) :=
  Array.ofFn (n := 192) bPair

@[expose] def yPow (j : Nat) : Array Nat × Array Nat :=
  if j = 0 then (idA, idA) else if j = 1 then (genA 4, genInvA 4)
  else (cmpA (genA 4) (genA 4), cmpA (genInvA 4) (genInvA 4))

@[expose] def p1Tab (_ : Unit := ()) : Array (Array Nat × Array Nat) :=
  let B := bTab ()
  Array.ofFn (n := 576) fun i =>
    let y := yPow (i.val / 192)
    let b := B.getD (i.val % 192) (idA, idA)
    (cmpA y.1 b.1, cmpA b.2 y.2)

@[expose] def p2Pair (k : Fin 960) : Array Nat × Array Nat :=
  (evalA (fun a : Fin 5 × Bool => letA (code2 a.1, a.2)) (h2Word k),
    evalA (fun a : Fin 5 × Bool => letA (code2 a.1, a.2)) (invWord (h2Word k)))

@[expose] def p2Tab (_ : Unit := ()) : Array (Array Nat × Array Nat) :=
  Array.ofFn (n := 960) p2Pair

@[expose] def fhatA' : Array Nat := fhatL.toArray

@[expose] def bhTab (_ : Unit := ()) : Array (Array Nat × Array Nat) :=
  let B := bTab ()
  B ++ B.map fun b => (cmpA b.1 fhatA', cmpA fhatA' b.2)

@[expose] def relOK4 (g : Fin 4 → Array Nat × Array Nat) (w : List (Fin 4 × Bool)) : Bool :=
  evalA (fun a => if a.2 then (g a.1).1 else (g a.1).2) w == idA

@[expose] def relOK5 (g : Fin 5 → Array Nat × Array Nat) (w : List (Fin 5 × Bool)) : Bool :=
  evalA (fun a => if a.2 then (g a.1).1 else (g a.1).2) w == idA

@[expose] def lvlOK (g : Fin 4 → Array Nat × Array Nat) (l : List Nat) : Bool :=
  l.all fun i => relOK4 g (relsB.getD i [])

@[expose] def conjA (f : Array Nat × Array Nat) (g : Array Nat) : Array Nat :=
  cmpA (cmpA f.1 g) f.2

@[expose] def conjMatch (f : Array Nat × Array Nat) (a b c d u v : Array Nat) : Bool :=
  conjA f (genA 0) == a && conjA f (genA 1) == b && conjA f (genA 2) == c &&
    conjA f (genA 3) == d && conjA f (genA 4) == u && conjA f (genA 5) == v

@[expose] def rigidCheck (_ : Unit := ()) : Bool :=
  let B := bTab ()
  let P1 := p1Tab ()
  let P2 := p2Tab ()
  let BH := bhTab ()
  let one : Array Nat × Array Nat := (idA, idA)
  B.all fun a =>
    !(lvlOK ![a, one, one, one] [0] && a.1 != idA) ||
    B.all fun b =>
      !(lvlOK ![a, b, one, one] [1, 5]) ||
      B.all fun c =>
        !(lvlOK ![a, b, c, one] [2, 6, 9]) ||
        B.all fun d =>
          !(lvlOK ![a, b, c, d] [3, 4, 7, 8, 10]) ||
          P1.all fun u =>
            !(rels1Extra.all fun w => relOK5 ![a, b, c, d, u] w) ||
            P2.all fun v =>
              !(rels2Extra.all fun w => relOK5 ![a, b, c, d, v] w) ||
              BH.any fun f => conjMatch f a.1 b.1 c.1 d.1 u.1 v.1

@[expose] def distinctTab (T : Array (Array Nat × Array Nat)) : Bool :=
  decide (T.toList.map Prod.fst).Nodup

@[expose] def bDistinct (_ : Unit := ()) : Bool := distinctTab (bTab ())

@[expose] def p1Distinct (_ : Unit := ()) : Bool := distinctTab (p1Tab ())

@[expose] def p2Distinct (_ : Unit := ()) : Bool := distinctTab (p2Tab ())

end CFSG.LargeExtraspecial.AS62.Rigid
