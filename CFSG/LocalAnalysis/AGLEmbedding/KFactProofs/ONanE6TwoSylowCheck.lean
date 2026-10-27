module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanE6TwoBits

public section

namespace CFSG.AGLEmbedding.E6Two

@[expose] def eqE (A B : ℕ) : Bool := A % 2 ^ 6084 == B % 2 ^ 6084

@[expose] def wordE (gb : Array ℕ) (w : List ℕ) : ℕ :=
  w.foldl (fun acc l => mulE acc gb[l]!) oneE

@[expose] def distinctE : List ℕ → Bool
  | [] => true
  | a :: l => l.all (fun b => !eqE a b) && distinctE l

@[expose] def bfsAuxE (gb : Array ℕ) :
    ℕ → List (List ℕ × ℕ) → List (List ℕ × ℕ) → List (List ℕ × ℕ)
  | 0, known, _ => known
  | fuel + 1, known, frontier =>
    if frontier.isEmpty then known else
    let st := frontier.foldl (fun (acc : List (List ℕ × ℕ) × List (List ℕ × ℕ)) p =>
      (List.range gb.size).foldl (fun (acc : List (List ℕ × ℕ) × List (List ℕ × ℕ)) k =>
        let v := mulE p.2 gb[k]!
        if acc.1.any (fun q => eqE q.2 v) then acc
        else ((p.1 ++ [k], v) :: acc.1, (p.1 ++ [k], v) :: acc.2)) acc) (known, [])
    bfsAuxE gb fuel st.1 st.2.reverse

@[expose] def bfsE (gb : Array ℕ) (fuel : ℕ) : List (List ℕ) :=
  ((bfsAuxE gb fuel [([], oneE)] [([], oneE)]).map Prod.fst).reverse

@[expose] def enumOKE (gb : Array ℕ) (L : List (List ℕ)) (vals : List ℕ) : Bool :=
  L.all (fun w => w.all fun l => decide (l < gb.size)) && decide (([] : List ℕ) ∈ L) &&
  vals.all (fun v => (List.range gb.size).all fun k => vals.any (eqE (mulE v gb[k]!))) &&
  distinctE vals

@[expose] def hasDistinctAux {α : Type} (f : α → ℕ) : ℕ → ℕ → List α → Bool
  | _, 0, _ => true
  | 0, _ + 1, _ => false
  | _ + 1, _ + 1, [] => false
  | fuel + 1, k + 1, a :: l =>
    hasDistinctAux f fuel k (l.filter fun b => !eqE (f a) (f b)) ||
      hasDistinctAux f fuel (k + 1) l

structure E6SylowData where
  sW : Array (List ℕ)
  sFuel : ℕ
  cW : Array (List ℕ)

@[expose] def sgB (X : E6SylowData) : Array ℕ := X.sW.map evalE

@[expose] def cLetters (X : E6SylowData) (c : List ℕ) : List ℕ := (c.map fun i => X.sW[i]!).flatten

@[expose] def cps (X : E6SylowData) : List (List ℕ) := X.cW.toList.map (cLetters X)

@[expose] def cpsB (X : E6SylowData) : List (List ℕ × ℕ × ℕ) :=
  (cps X).map fun lw => (lw, evalE lw, evalE lw.reverse)

@[expose] def conjP (v : ℕ) (p : List ℕ × ℕ × ℕ) : ℕ := mulE (mulE p.2.1 v) p.2.2

@[expose] def goodB (cp : List (List ℕ × ℕ × ℕ)) (v : ℕ) : Bool :=
  hasDistinctAux (conjP v) cp.length 4 cp

@[expose] def badWords (gb : Array ℕ) (L : List (List ℕ)) (cp : List (List ℕ × ℕ × ℕ)) :
    List (List ℕ) :=
  L.filter fun w => !goodB cp (wordE gb w)

@[expose] def e6SylowCheck' (X : E6SylowData) (gb : Array ℕ) (L : List (List ℕ)) (V : List ℕ)
    (cp : List (List ℕ × ℕ × ℕ)) : Bool :=
  X.cW.toList.all (fun c => c.all fun i => decide (i < X.sW.size)) &&
  enumOKE gb L V && decide (L.length = 729) && decide ((badWords gb L cp).length < 243)

@[expose] def e6SylowCheck (X : E6SylowData) : Bool :=
  let gb := sgB X
  let L := bfsE gb X.sFuel
  e6SylowCheck' X gb L (L.map (wordE gb)) (cpsB X)

end CFSG.AGLEmbedding.E6Two
