module

public import Certificates.Data.CFSGNative.Schreier.Check

public section

namespace CFSG.EvenSmallLie.Child3

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def powN (n : Nat) (t : Array Nat) : Nat → Array Nat
  | 0 => idA n
  | k + 1 => compA n t (powN n t k)

@[expose] def conjA (n : Nat) (g x : Array Nat) : Array Nat := compA n (compA n g x) (invCand n g)

@[expose] def witOK (n : Nat) (y w : Array Nat) : Bool :=
  eqA n (compA n w y) (compA n y w) && !eqA n (powN n w 4) (idA n) &&
    !eqA n (powN n w 6) (idA n) && !eqA n (powN n w 14) (idA n)

@[expose] def stabOK (n : Nat) (S : Array (Array Nat)) (r : Nat) (ws : List (List Int)) : Bool :=
  let vs := ws.map (wordA n S (rawInvs n S))
  decide (r < n) && ws.all (lettersOK S.size) && vs.all (fun v => v[r]! == r) &&
    allLt n fun q => q == r || vs.any fun v => v[q]! != q

@[expose] def forestOK (n : Nat) (S : Array (Array Nat)) (roots : List Nat)
    (par lab dep : Array Nat) : Bool :=
  allLt n fun p => (dep[p]! == 0 && roots.contains p) ||
    (decide (par[p]! < n) && decide (lab[p]! < S.size) && decide (dep[par[p]!]! < dep[p]!) &&
      (S[lab[p]!]!)[par[p]!]! == p)

@[expose] def bfsForest (n : Nat) (S : Array (Array Nat)) (roots : List Nat) :
    Array Nat × Array Nat × Array Nat := Id.run do
  let mut par : Array Nat := Array.replicate n 0
  let mut lab : Array Nat := Array.replicate n 0
  let mut dep : Array Nat := Array.replicate n (n + 1)
  let mut queue : Array Nat := #[]
  for r in roots do
    dep := dep.set! r 0
    queue := queue.push r
  let mut h := 0
  for _ in [0:n] do
    if h < queue.size then
      let x := queue[h]!
      h := h + 1
      for l in [0:S.size] do
        let y := (S[l]!)[x]!
        if y < n && dep[y]! == n + 1 then
          dep := dep.set! y (dep[x]! + 1)
          par := par.set! y x
          lab := lab.set! y l
          queue := queue.push y
  return (par, lab, dep)

@[expose] def centOK (n : Nat) (S : Array (Array Nat)) (rs : List (Nat × List (List Int))) : Bool :=
  let F := bfsForest n S (rs.map Prod.fst)
  rs.all (fun r => stabOK n S r.1 r.2) && forestOK n S (rs.map Prod.fst) F.1 F.2.1 F.2.2

end CFSG.EvenSmallLie.Child3
