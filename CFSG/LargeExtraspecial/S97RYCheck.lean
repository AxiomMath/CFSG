module

public import CFSG.CGT.Timmesfeld75.ListWCPermCheck

public section

namespace CFSG.LargeExtraspecial.S11.PairCheck

open CFSG.Sporadic.Th.Native CFSG.CGT.Timmesfeld75.WCCheck

inductive PVerdict where
  | size
  | notClosed (i j : Nat)
  | bad (t y : Nat) (g : List Int)
  | good (c : List Int) (nIdx : List Nat) (out : List Int)

structure PData where
  D : Data
  ord : Nat
  nCount : Nat
  proper : Bool
  fuel : Nat
  pv : List (List Bool × PVerdict)

@[expose] def baseCheck (D : Data) : Bool :=
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
        conjT n (wT D p.2) (wT D (invWord p.2)) (el D i₀) == el D p.1)

@[expose] def tabU (D : Data) (J : List Bool) : List Table := idT D.n :: (idxU D J).map (el D)

@[expose] def conjW (D : Data) (c : List Int) (t : Table) : Table :=
  conjT D.n (wT D c) (wT D (invWord c)) t

@[expose] def tabUc (D : Data) (J : List Bool) (c : List Int) : List Table :=
  (tabU D J).map (conjW D c)

@[expose] def normU (D : Data) (J : List Bool) (c : List Int) (x : Table) : Bool :=
  (tabUc D J c).all fun t => memL (tabUc D J c) (conjT D.n x x t)

@[expose] def closeRound (n : Nat) (gs : List Table) (E fr : List Table) :
    List Table × List Table :=
  fr.foldl (fun acc x => gs.foldl (fun acc s =>
    let y := compT n x s
    if memL acc.1 y then acc else (y :: acc.1, y :: acc.2)) acc) (E, [])

@[expose] def closeT (n : Nat) (gs : List Table) : Nat → List Table → List Table → List Table
  | 0, E, _ => E
  | fuel + 1, E, fr =>
    let r := closeRound n gs E fr
    if r.2.isEmpty then r.1 else closeT n gs fuel r.1 r.2

@[expose] def properOK (D : Data) (fuel : Nat) (J : List Bool) (c out : List Int) : Bool :=
  let gs := tabU D J ++ tabUc D J c
  let E := closeT D.n gs fuel [idT D.n] [idT D.n]
  memL E (idT D.n) &&
    (E.all fun x => x.size == D.n && gs.all fun s => memL E (compT D.n x s)) &&
    !memL E (wT D out)

@[expose] def pverdictOK (P : PData) (J : List Bool) : PVerdict → Bool
  | .size => (idxU P.D J).length + 1 != P.ord
  | .notClosed i j => verdictOK P.D J (.notClosed i j)
  | .bad t y g => (idxU P.D J).contains t && (idxU P.D J).contains y &&
      !(el P.D t == idT P.D.n) &&
      ((tabU P.D J).all fun u => commT P.D.n (conjW P.D g u) (el P.D t)) &&
      !memU P.D J (conjW P.D g (el P.D y))
  | .good c nIdx out => (idxU P.D J).length + 1 == P.ord && nIdx.length == P.nCount &&
      decide nIdx.Nodup && (nIdx.all fun i => (idxU P.D J).contains i) &&
      ((idxU P.D J).all fun i => nIdx.contains i == normU P.D J c (el P.D i)) &&
      (!P.proper || properOK P.D P.fuel J c out)

@[expose] def pairCheck (P : PData) : Bool :=
  decide (P.D.n < 2 ^ 32) && decide (2 ≤ P.ord) && baseCheck P.D &&
    (allMasks P.D.cls.length).all fun J => P.pv.any fun p => p.1 == J && pverdictOK P J p.2

end CFSG.LargeExtraspecial.S11.PairCheck
