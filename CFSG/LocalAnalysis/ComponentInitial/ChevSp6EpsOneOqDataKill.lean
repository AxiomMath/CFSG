module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneOqData

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne

@[expose] def omT : List ℕ := (List.range 6).map fun j =>
  mkv (xpart (2 ^ j)) (wpart (2 ^ j) ^^^ xpart (2 ^ j))

@[expose] def imNl (l : List ℕ) : List ℕ := (List.range 3).map fun i => evalV l (mkv 0 (2 ^ i))

@[expose] def imNr (l : List ℕ) : List ℕ :=
  (List.range 3).map fun i => evalV l (mkv (2 ^ i) (2 ^ i))

@[expose] def presT (u : Bool) (l : List ℕ) : Bool :=
  if u then compT l omT == compT omT l else (imNl l).all fun v => wpart v == 0

@[expose] def sgnOK (u : Bool) (l : List ℕ) : Bool :=
  if u then compT l omT == compT omT l || compT l omT == compT (compT omT omT) l
  else ((imNl l).all (fun v => wpart v == 0) && (imNr l).all (fun v => wpart v == xpart v)) ||
    ((imNl l).all (fun v => wpart v == xpart v) && (imNr l).all (fun v => wpart v == 0))

@[expose] def isInvT (l : List ℕ) : Bool := compT l l == idT && l != idT

@[expose] def letter (l : List ℕ) : ℕ → List ℕ
  | 0 => z0T
  | 1 => lam1T
  | 2 => lam2T
  | _ => l

@[expose] def evalW (l : List ℕ) (w : List ℕ) : List ℕ :=
  w.foldl (fun acc a => compT acc (letter l a)) idT

@[expose] def bfsAux (gens : List (List ℕ)) :
    ℕ → List (List ℕ × List ℕ) → List (List ℕ × List ℕ) → List (List ℕ × List ℕ)
  | 0, known, _ => known
  | n + 1, known, fr =>
    let new := fr.foldl (fun acc p => (List.range gens.length).foldl (fun acc i =>
      let y := compT p.1 (gens.getD i [])
      if (known.any fun q => q.1 == y) || (acc.any fun q => q.1 == y) then acc
      else acc ++ [(y, p.2 ++ [i])]) acc) []
    if new.isEmpty then known else bfsAux gens n (known ++ new) new

@[expose] def killReps (u : Bool) : List (List ℕ × List (List ℕ)) :=
  if u then
    [([1, 2, 4, 8, 17, 34], [[3], [1], [0], [2, 1, 2, 2]]),
     ([1, 2, 4, 8, 18, 35], [[3], [1], [0, 3, 0], [2, 1, 2, 2]]),
     ([1, 2, 4, 8, 22, 43], [[3], [0, 1], [0, 3, 0], [2, 1, 2, 2]]),
     ([1, 2, 5, 10, 18, 35], [[3], [1], [0, 3, 0], [0, 2, 1, 2, 2]]),
     ([1, 2, 24, 44, 40, 60], [[3], [1, 3, 1], [2, 1, 3, 0, 2, 2, 3, 0, 2],
       [0, 2, 3, 0, 3, 0, 1, 2, 3, 0, 1]])]
  else
    [([1, 2, 4, 8, 17, 34], [[3], [1], [0], [2, 1, 2, 2]]),
     ([1, 2, 4, 8, 18, 34], [[3], [1], [0, 3, 0], [2, 1, 2, 2], [2, 3, 2, 2, 3, 2, 3, 2, 2],
       [2, 2, 3, 2, 3, 2, 2, 3, 2]]),
     ([1, 2, 4, 8, 22, 42], [[3], [0, 1], [0, 3, 0], [2, 1, 2, 2]]),
     ([1, 2, 5, 10, 18, 34], [[3], [1], [0, 3, 0], [0, 2, 1, 2, 2]]),
     ([1, 2, 6, 10, 28, 32], [[3], [1, 3, 1], [0, 1, 3, 1, 3, 0],
       [2, 3, 1, 3, 2, 2, 1, 3, 1, 2, 3, 1, 3, 2, 2]]),
     ([1, 2, 24, 40, 44, 32], [[3], [1, 3, 1], [0, 2, 2, 1, 3, 1, 3, 0, 2],
       [1, 2, 2, 3, 0, 1, 3, 0, 1, 3, 2]])]

@[expose] def fixV (l : List ℕ) : List ℕ := (List.range 64).filter fun v => evalV l v == v

@[expose] def validCert (u : Bool) (l : List ℕ) (c : List (List ℕ) × ℕ × ℕ) : Bool :=
  let els := c.1.map (evalW l)
  let n := els.length
  let codes := els.map codeT
  let B := bOf u l
  let fe := ((List.range 512).filter fun e => evalE B e == e).length
  0 < n && (List.range 9).any (fun k => n == 2 ^ k) && decide codes.Nodup &&
    codes.contains (codeT idT) &&
    codes.contains (codeT l) &&
    els.all (fun a => els.all fun b => codes.contains (codeT (compT a b))) &&
    els.all (fun a => compT a l == compT l a) &&
    (fixV l).length * fe ≤ 32 * n &&
    c.2.1 < 64 && c.2.2 < 64 && evalV l c.2.1 == c.2.1 && evalV l c.2.2 == c.2.2 &&
    !((List.range 512).any fun e => evalE B e ^^^ e == betaOf u c.2.1 c.2.2)

@[expose] def idE : List ℕ := [1, 2, 4, 8, 16, 32, 64, 128, 256]

end CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne
