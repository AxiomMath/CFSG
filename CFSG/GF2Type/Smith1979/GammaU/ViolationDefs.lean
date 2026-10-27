module

public import CFSG.GF2Type.Smith1979.GammaU.StepAInputs

public section

namespace CFSG.GF2Type.Smith1979.GammaU.Viol

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA

@[expose] def invR (r : Array ℕ) : Array ℕ :=
  ((List.range 12).map fun j =>
    ((List.range 4096).find? fun n => appN r n == 2 ^ j).getD 0).toArray

abbrev St : Type := ℕ × Array ℕ × Array ℕ

@[expose] def stepOf (p : Array ℕ × Array ℕ) (s : St) : St :=
  (appN p.1 s.1, mulR p.1 s.2.1, mulR s.2.2 p.2)

@[expose] def withInv (gs : List (Array ℕ)) : List (Array ℕ × Array ℕ) :=
  gs.map fun g => (g, invR g)

@[expose] def orbitTr (W : List (Array ℕ × Array ℕ)) : List St :=
  bfsClosure (fun s : St => s.1) (W.map stepOf) 4096 [(a0, idR, idR)]
    ((∅ : Std.HashSet ℕ).insert a0) []

@[expose] def okRows (r : Array ℕ) : Bool := r.size == 12 && r.all (· < 4096)

@[expose] def d1Check (W : List (Array ℕ × Array ℕ)) (O : List St) (Lc Lg : List (Array ℕ)) :
    Bool :=
  O.any fun s => W.any fun p =>
    let y := appN p.1 s.1
    match O.find? (fun t => t.1 == y) with
    | none => false
    | some t =>
      let h := mulR t.2.2 (mulR p.1 s.2.1)
      let hi := mulR s.2.2 (mulR p.2 t.2.1)
      appN h a0 == a0 && Lg.any fun l => !(Lc.contains (mulR h (mulR l hi)))

@[expose] def ptsOf (O : List St) (Lc : List (Array ℕ)) (s : Array ℕ) : List ℕ :=
  O.filterMap fun t => if Lc.contains (mulR t.2.2 (mulR s t.2.1)) then some (appN t.2.1 a0)
    else none

@[expose] def f4Indep (x y : ℕ) : Bool :=
  x != 0 && y != 0 && y != x && y != theta0N x && y != (x ^^^ theta0N x)

@[expose] def f2Indep3 (x y w : ℕ) : Bool :=
  x != 0 && y != 0 && y != x && w != 0 && w != x && w != y && w != (x ^^^ y)

@[expose] def d2uCheck (O : List St) (Lc H : List (Array ℕ)) : Bool :=
  Lc.any fun s => unitaryN s && !(H.contains s) &&
    let P := ptsOf O Lc s
    P.any fun x => P.any fun y => f4Indep x y

@[expose] def d2aCheck (O : List St) (Lc : List (Array ℕ)) : Bool :=
  Lc.any fun s => antiN s &&
    let P := ptsOf O Lc s
    P.any fun x => P.any fun y => P.any fun w => f2Indep3 x y w

@[expose] def pairOK (p : Array ℕ × Array ℕ) : Bool :=
  okRows p.1 && okRows p.2 && mulR p.1 p.2 == idR && mulR p.2 p.1 == idR

@[expose] def violCheckW (W : List (Array ℕ × Array ℕ)) (Lc Lg H : List (Array ℕ))
    (d1First : Bool) : Bool :=
  W.all pairOK && Lc.all okRows && Lg.all Lc.contains &&
    let O := orbitTr W
    if d1First then d1Check W O Lc Lg || d2uCheck O Lc H || d2aCheck O Lc
    else d2uCheck O Lc H || d2aCheck O Lc || d1Check W O Lc Lg

@[expose] def violCheck (gs Lc Lg H : List (Array ℕ)) : Bool :=
  violCheckW (withInv gs) Lc Lg H false

end CFSG.GF2Type.Smith1979.GammaU.Viol
