module

public import Certificates.Data.CFSGNative.Th.Tables

public section

namespace CFSG.CGT.Timmesfeld75.WCCheck

open CFSG.Sporadic.Th.Native

inductive Verdict where
  | small
  | notClosed (i j : Nat)
  | bad (t y : Nat) (g : List Int)
  | good (d : List (List Int))

structure Data where
  n : Nat
  gens : Int → Table
  pc : List (List Int)
  zIdx : Nat
  cw : List (List Int)
  cls : List (List (Nat × List Int))
  verdicts : List (List Bool × Verdict)

@[expose] def invWord (w : List Int) : List Int := (w.map Neg.neg).reverse

@[expose] def wT (D : Data) (w : List Int) : Table := wordT D.n D.gens w

@[expose] def eltT (n : Nat) : List Table → Nat → Table
  | [], _ => idT n
  | s :: ss, m => compT n (if m % 2 = 1 then s else idT n) (eltT n ss (m / 2))

@[expose] def pcT (D : Data) : List Table := D.pc.map (wT D)

@[expose] def elts (D : Data) : List Table :=
  (List.range (2 ^ D.pc.length)).map (eltT D.n (pcT D))

@[expose] def el (D : Data) (i : Nat) : Table := eltT D.n (pcT D) i

@[expose] def memL (S : List Table) (t : Table) : Bool := S.any (· == t)

@[expose] def memS (D : Data) (t : Table) : Bool := memL (elts D) t

@[expose] def commT (n : Nat) (x y : Table) : Bool := compT n x y == compT n y x

@[expose] def conjT (n : Nat) (g gi x : Table) : Table := compT n (compT n g x) gi

@[expose] def cwT (D : Data) : List (Table × Table) :=
  D.cw.map fun w => (wT D w, wT D (invWord w))

@[expose] def excl (n : Nat) (S : List Table) (cws : List (Table × Table)) (x : Table) : Bool :=
  !(compT n x x == idT n) ||
    S.any (fun y => !commT n x (conjT n y (invT n y) x)) ||
    cws.any (fun g => let c := conjT n g.1 g.2 x
      !memL S c || !commT n x c)

@[expose] def allMasks : Nat → List (List Bool)
  | 0 => [[]]
  | r + 1 => (allMasks r).flatMap fun l => [false :: l, true :: l]

@[expose] def selCls (D : Data) (J : List Bool) : List (List (Nat × List Int)) :=
  ((D.cls.zip J).filter fun p => p.2).map Prod.fst

@[expose] def idxU (D : Data) (J : List Bool) : List Nat :=
  D.zIdx :: ((selCls D J).flatMap fun c => c.map Prod.fst)

@[expose] def memU (D : Data) (J : List Bool) (t : Table) : Bool :=
  t == idT D.n || (idxU D J).any fun i => el D i == t

@[expose] def verdictOK (D : Data) (J : List Bool) : Verdict → Bool
  | .small => (idxU D J).length + 1 < 4
  | .notClosed i j => (idxU D J).contains i && (idxU D J).contains j &&
      !memU D J (compT D.n (el D i) (el D j))
  | .bad t y g => (idxU D J).contains t && (idxU D J).contains y &&
      !(el D t == idT D.n) && commT D.n (wT D g) (el D t) &&
      !memU D J (conjT D.n (wT D g) (wT D (invWord g)) (el D y))
  | .good d => (idxU D J).length + 1 == 16 && d.length == (selCls D J).length &&
      ((d.zip (selCls D J)).all fun q =>
        match q.2 with
        | [] => false
        | (i, _) :: _ => conjT D.n (wT D q.1) (wT D (invWord q.1)) (el D D.zIdx) == el D i)

@[expose] def wcCheck (D : Data) : Bool :=
  let n := D.n
  let S := elts D
  let k := D.pc.length
  let z := el D D.zIdx
  decide S.Nodup &&
  (S.all fun x => (pcT D).all fun s => memL S (compT n x s)) &&
  (S.all fun x => D.pc.all fun w => memL S (compT n x (wT D (invWord w)))) &&
  (S.all fun x => invOK n x (invT n x)) &&
  decide (D.zIdx < 2 ^ k) && !(z == idT n) && compT n z z == idT n &&
  ((pcT D).all fun s => commT n z s) &&
  (S.all fun x => !((pcT D).all fun s => commT n x s) || x == idT n || x == z) &&
  (D.cw.all fun w => commT n (wT D w) z) &&
  (S.all fun x => x == idT n || x == z || (D.cls.any fun c => c.any fun p => el D p.1 == x) ||
    excl n S (cwT D) x) &&
  decide (0 :: D.zIdx :: (D.cls.flatMap fun c => c.map Prod.fst)).Nodup &&
  ((D.cls.flatMap fun c => c.map Prod.fst).all fun i => decide (i < 2 ^ k)) &&
  (D.cls.all fun c => match c with
    | [] => false
    | (i₀, _) :: _ => c.all fun p => commT n (wT D p.2) z &&
        conjT n (wT D p.2) (wT D (invWord p.2)) (el D i₀) == el D p.1) &&
  ((allMasks D.cls.length).all fun J => D.verdicts.any fun p => p.1 == J && verdictOK D J p.2)

end CFSG.CGT.Timmesfeld75.WCCheck
