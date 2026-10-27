module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneOqDataKill

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne

@[expose] def pGens (u : Bool) : List (List ℕ) :=
  if u then
    [[1, 3, 4, 12, 16, 48], [1, 2, 5, 10, 16, 32], [1, 2, 4, 8, 20, 40], [1, 2, 4, 8, 18, 35],
     [1, 2, 4, 8, 24, 44], [1, 2, 6, 11, 16, 32]]
  else
    [[1, 3, 4, 12, 16, 48], [1, 2, 5, 10, 16, 32], [1, 2, 4, 8, 20, 40], [1, 2, 4, 8, 18, 34],
     [1, 2, 4, 8, 24, 40], [1, 2, 6, 10, 16, 32]]

@[expose] def pList (u : Bool) : List (List ℕ) :=
  (bfsAux (pGens u) 40 [(idT, [])] [(idT, [])]).map Prod.fst

@[expose] def insCode (a : List ℕ) : List (List ℕ) → List (List ℕ)
  | [] => [a]
  | b :: l => if codeT a < codeT b then a :: b :: l else if codeT a = codeT b then b :: l
    else b :: insCode a l

@[expose] def adjoin (x : List ℕ) (A : List (List ℕ)) : List (List ℕ) :=
  (A ++ A.map (compT x)).foldr insCode []

@[expose] def extenders (P A : List (List ℕ)) : List (List ℕ) :=
  P.filter fun x => isInvT x && !(A.contains x) && A.all fun a => compT x a == compT a x

@[expose] def eaClose (P : List (List ℕ)) : ℕ → List (List (List ℕ)) → List (List (List ℕ)) →
    List (List (List ℕ))
  | 0, known, _ => known
  | n + 1, known, fr =>
    let new := fr.foldl (fun acc A => (extenders P A).foldl (fun acc x =>
      let B := adjoin x A
      if known.contains B || acc.contains B then acc else acc ++ [B]) acc) []
    if new.isEmpty then known else eaClose P n (known ++ new) new

@[expose] def eaList (u : Bool) : List (List (List ℕ)) := eaClose (pList u) 10 [[idT]] [[idT]]

@[expose] def pCheck (u : Bool) : Bool :=
  let P := pList u
  P.length == 128 && decide (P.map codeT).Nodup && P.contains idT &&
    P.all (validT u) && P.all fun a => P.all fun b => P.contains (compT a b)

@[expose] def eaCheck (u : Bool) : Bool :=
  let P := pList u
  let EL := eaList u
  EL.contains [idT] && EL.all fun A =>
    A.all P.contains && decide (A.map codeT).Nodup && A.contains idT &&
      (extenders P A).all fun x => EL.contains (adjoin x A) && A.length < (adjoin x A).length

@[expose] def boundCheck (u : Bool) : Bool :=
  let EL := eaList u
  EL.all fun A => A == [idT] ||
    let Bs := A.map (bOf u)
    A.length * ((List.range 512).filter fun e => Bs.all fun B => evalE B e == e).length *
      ((List.range 64).filter fun v => qOf u v == 0 && A.all fun a => evalV a v == v).length <
      2 ^ (if u then 9 else 12)

end CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne
