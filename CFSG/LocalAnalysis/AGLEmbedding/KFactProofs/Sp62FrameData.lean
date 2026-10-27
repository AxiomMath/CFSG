module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62EscapeData
public meta import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62EscapeData

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sp62Local

open CFSG.KGroups.Sp6 CFSG.Quasithin.G2U

@[expose] def cIo1 : List ℕ := [1, 16, 4, 8, 2, 32]

@[expose] def cIo2 : List ℕ := [1, 2, 32, 8, 16, 4]

@[expose] def cTau12 : List ℕ := [1, 4, 2, 8, 32, 16]

@[expose] def gensS0 : List (List ℕ) := [cW0, cW1, cW2, cIo, cIo1, cIo2, cTau12]

@[expose] def gensX : List (List ℕ) := gensT ++ gensAlt ++ [cIo1, cTau12]

@[expose] def letterL (L : List (List ℕ)) (l : ℕ × Bool) : List ℕ :=
  if l.2 then L.getD l.1 oneC else invC (L.getD l.1 oneC)

@[expose] def evalWordC (L : List (List ℕ)) (w : List (ℕ × Bool)) : List ℕ :=
  w.foldr (fun l acc => mulC (letterL L l) acc) oneC

@[expose] def wordTau : List (ℕ × Bool) := [(9, false), (3, false)]

@[expose] def wordIo : List (ℕ × Bool) := [(3, false), (8, false), (3, true)]

@[expose] def wordGD : List (ℕ × Bool) :=
  [(8, false), (1, false), (9, false), (4, true), (2, true), (4, false), (3, true), (7, true),
    (3, true), (4, false), (3, true), (5, true), (3, false), (4, false), (6, false)]

@[expose] def dcPairs : List (List ℕ × List (ℕ × Bool)) :=
  [([49, 42, 28, 8, 16, 32],
    [(3, true), (5, false), (3, false), (1, false), (6, false), (1, false), (6, false), (0, true),
      (2, true), (6, false), (1, true)]),
   ([29, 53, 23, 62, 14, 56],
    [(4, false), (1, false), (6, false), (2, true), (6, false), (2, false), (0, false),
      (6, false), (5, false), (0, false), (6, true)]),
   ([1, 34, 20, 8, 16, 32],
    [(5, false), (0, false), (3, false), (6, true), (1, true), (6, true), (2, false), (6, false),
      (3, true), (0, true), (6, false), (4, false), (6, false), (1, true), (6, false), (0, false),
      (2, true), (6, false), (4, false), (6, false), (1, true)]),
   ([49, 10, 12, 8, 16, 32],
    [(0, true), (6, false), (1, false), (6, false), (1, true), (6, true), (1, true), (0, true),
      (6, false), (1, false), (3, false), (0, true), (6, false), (3, true), (1, true)]),
   ([21, 54, 20, 8, 16, 56],
    [(0, false), (2, true), (6, false), (0, false), (6, true), (2, false), (4, false), (3, false),
      (0, false), (6, true), (0, true), (1, true), (3, true), (6, false)]),
   ([21, 40, 10, 8, 14, 56],
    [(3, false), (5, false), (3, true), (6, true), (1, false), (2, false), (6, false), (6, false),
      (1, true), (1, true), (3, false), (4, true), (6, true), (1, true), (6, false), (2, false),
      (0, true), (6, false), (3, false)]),
   ([29, 13, 25, 62, 14, 56],
    [(1, true), (5, false), (0, false), (3, false), (6, true), (6, true), (3, true), (6, false)])]

@[expose] def dcReps : List (List ℕ) := oneC :: dcPairs.map Prod.fst

@[expose] def commC (x n : List ℕ) : List ℕ := mulC x (mulC n (mulC (invC x) (invC n)))

@[expose] def propN0 (tabN : Array (List ℕ)) : Bool := allCheck genB tabN

@[expose] def propN1 (tabN : Array (List ℕ)) : Bool :=
  let tabB := tabOf gensB 27
  allCheck (fun x => !(gensB.all (commB x)) || inTab tabB x) tabN

@[expose] def irrOK (w : List ℕ) : Bool :=
  [(cIo, cW0), (cIo1, cW1), (cIo2, cW2)].any fun p =>
    let v := mulC w (conjC p.1 (invC w))
    v == p.2 || v == invC p.2

@[expose] def propN2 (_ : Array (List ℕ)) : Bool :=
  let tabB := tabOf gensB 27
  allCheck genB tabB && allCheck (fun w => w == oneC || irrOK w) tabB &&
    conjC cSg cW0 == cW1 && conjC cSg cW1 == cW2 && conjC cSg cW2 == cW0

@[expose] def propN3 (tabN : Array (List ℕ)) : Bool :=
  let tabB := tabOf gensB 27
  allCheck (fun x => inTab tabB x || powC x 81 != oneC ||
    tabN.any fun n => powC (commC x n) 81 != oneC) tabN

@[expose] def propN4 (tabN : Array (List ℕ)) : Bool :=
  [cIo1, cIo2, cTau12].all (inTab tabN)

@[expose] def propN (tabN : Array (List ℕ)) : Bool :=
  propN0 tabN && propN1 tabN && propN2 tabN && propN3 tabN && propN4 tabN

@[expose] def chkN (_ : Unit := ()) : Bool := tabCheck gensN 1296 propN

@[expose] def propTT (tabT : Array (List ℕ)) : Bool :=
  let tabB := tabOf gensB 27
  allCheck genB tabT &&
  allCheck (fun c => inZ c || tabT.all fun t => !(commB c t) || inTab tabB t) tabB &&
  allCheck (fun x => powC x 9 == oneC) tabT &&
  allCheck (fun x => powC x 3 == oneC ||
    tabT.any fun t => !((List.range 9).any fun k => conjC t x == powC x k)) tabT &&
  !(inTab tabB cSg) && gensT.all (commB cZ) &&
  allCheck (fun x => !(gensB.all (commB x)) || inTab tabB x) tabT

@[expose] def chkTT (_ : Unit := ()) : Bool := tabCheck gensT 81 propTT

@[expose] def propS0 (_ : Array (List ℕ)) : Bool :=
  let tabN := tabOf gensN 1296
  let w2 := mulC cW0 cW0
  gensS0.all (fun g => inTab tabN g && (conjC g cW0 == cW0 || conjC g cW0 == w2)) &&
    !(conjC cSg cW0 == cW0 || conjC cSg cW0 == w2)

@[expose] def chkS0 (_ : Unit := ()) : Bool := tabCheck gensS0 432 propS0

@[expose] def chkWordsX (_ : Unit := ()) : Bool :=
  let tabB := tabOf gensB 27
  gensX.all genB && [cIo1, cTau12].all (commB cW0) &&
  evalWordC gensX wordTau == cTau && evalWordC gensX wordIo == cIo &&
  evalWordC gensX wordGD == cGD &&
  dcPairs.all fun p => genB p.1 && !(gensB.all fun g => inTab tabB (conjC p.1 g))

@[expose] def chkDCWords (_ : Unit := ()) : Bool :=
  dcPairs.all fun p => evalWordC (gensN ++ [p.1]) p.2 == cGD

@[expose] def planeKey (a b : ℕ) : ℕ :=
  let w := a ^^^ b
  (min a (min b w)) * 64 + (max a (max b w))

@[expose] def decKey (c : List ℕ) : ℕ :=
  let p := planeKey (c.getD 0 0) (c.getD 3 0)
  let q := planeKey (c.getD 1 0) (c.getD 4 0)
  let r := planeKey (c.getD 2 0) (c.getD 5 0)
  let lo := min p (min q r)
  let hi := max p (max q r)
  lo + 4096 * (p + q + r - lo - hi) + 4096 * 4096 * hi

@[expose] def dcTable (tabN : Array (List ℕ)) : Std.HashMap ℕ (List ℕ × List ℕ × List ℕ) :=
  dcReps.foldl (fun m r =>
    let rinv := invC r
    tabN.foldl (fun m n => m.insert (decKey (mulC n r)) (r, rinv, invC n)) m) {}

@[expose] def chkDC (_ : Unit := ()) : Bool :=
  let tabN := tabOf gensN 1296
  let hsN : Std.HashSet (List ℕ) := Std.HashSet.ofList tabN.toList
  let tbl := dcTable tabN
  dcReps.all genB &&
  (spCount 64 fun c =>
    match tbl.get? (decKey c) with
    | some (r, rinv, m) => !(dcReps.contains r && validB rinv && mulC r rinv == oneC &&
        hsN.contains m && hsN.contains (mulC rinv (mulC m c)))
    | none => true) == 0

@[expose] def czCheck (tabW : Array (List ℕ)) : Bool :=
  let hsW : Std.HashSet (List ℕ) := Std.HashSet.ofList tabW.toList
  (spCount 64 fun c => commB c cZ && !hsW.contains c) == 0

@[expose] def chkCz (_ : Unit := ()) : Bool := czCheck (tabOf gensWD 51840)

end CFSG.AGLEmbedding.KFactProofs.Sp62Local
