module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentDefs
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentTree
public meta import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentDefs
public meta import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentTree
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.Co3Schreier.Basic

public section

namespace CFSG.EvenSmallLie.SympSix.Co3Ident

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Co3
  CFSG.Sporadic.Schreier.Co3.Native Subgroup

@[expose] def letArr (l : Fin 7 × Bool) : Array ℕ :=
  if l.2 then genArr l.1 else invCand 276 (genArr l.1)

@[expose] def wordArr : List (Fin 7 × Bool) → Array ℕ
  | [] => idA 276
  | l :: w => compA 276 (letArr l) (wordArr w)

@[expose] def posArr (l : List (Fin 7)) : Array ℕ := wordArr (pos l)

@[expose] def edgeFirst (k : ℕ) : List (Fin 7) := (edgePairs.getD k ([], [])).1

@[expose] def gPaths : List (List ℕ) := [[3, 4, 3, 5], [2, 3, 5], [2, 5, 3]]

@[expose] def gLetters (i : ℕ) : List (Fin 7) := (gPaths.getD i []).flatMap edgeFirst

@[expose] def gArrs : Array (Array ℕ) := Array.ofFn (n := 3) fun i => posArr (gLetters i)

@[expose] def hKey (t : Array ℕ) : ℕ := keyOf [0, 1] t

irreducible_def hBFS : Array (Array ℕ) × Array ℕ × Array ℕ × Array ℕ := Id.run do
  let mut HL : Array (Array ℕ) := #[idA 276]
  let mut par : Array ℕ := #[0]
  let mut lab : Array ℕ := #[0]
  let mut pos : Array ℕ := (Array.replicate (276 * 276) 0).set! (hKey (idA 276)) 1
  for q in [0:4608] do
    if q < HL.size then
      for i in [0:3] do
        let y := compA 276 HL[q]! gArrs[i]!
        let k := hKey y
        if pos[k]! == 0 then
          HL := HL.push y
          par := par.push q
          lab := lab.push i
          pos := pos.set! k HL.size
  return (HL, par, lab, pos)

@[expose] def hList : Array (Array ℕ) := hBFS.1
@[expose] def hPar : Array ℕ := hBFS.2.1
@[expose] def hLab : Array ℕ := hBFS.2.2.1

@[expose] def cBFS : Array (Array ℕ) × Array ℕ × Array ℕ := Id.run do
  let mut CL : Array (Array ℕ) := #[genArr 0]
  let mut par : Array ℕ := #[0]
  let mut lab : Array ℕ := #[0]
  let mut seen : Std.HashSet ℕ := (∅ : Std.HashSet ℕ).insert (keyOf [0, 1, 2, 3] (genArr 0))
  for q in [0:630] do
    if q < CL.size then
      for k in [0:7] do
        let m := co3MArrs[k]!
        let y := compA 276 (invCand 276 m) (compA 276 CL[q]! m)
        let key := keyOf [0, 1, 2, 3] y
        if !seen.contains key then
          seen := seen.insert key
          CL := CL.push y
          par := par.push q
          lab := lab.push k
  return (CL, par, lab)

@[expose] def conjTabOK (n : ℕ) (G Gi : Array (Array ℕ)) (par lab : Array ℕ)
    (T : Array (Array ℕ)) (t₀ : Array ℕ) (N : ℕ) : Bool :=
  eqA n T[0]! t₀ && allLt N fun j => j == 0 ||
    (decide (par[j]! < j) && decide (lab[j]! < G.size) &&
      eqA n T[j]! (compA n Gi[lab[j]!]! (compA n T[par[j]!]! G[lab[j]!]!)))

@[expose] def mGenArrs : Array (Array ℕ) := co3MArrs.extract 0 7

end CFSG.EvenSmallLie.SympSix.Co3Ident
