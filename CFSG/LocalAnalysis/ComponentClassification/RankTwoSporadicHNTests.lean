
module

public import CFSG.Sporadic.HNOddCore.SylCBase
public import CFSG.RankThree.Native.PermEnumeration

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.HN

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native CFSG.Sporadic.F5.Native
open CFSG.Sporadic.HNOddCore CFSG.RankThree.Native CFSG.Monster.B.Fischer
open CFSG.Monster.B.Co2.Native

@[expose] def invW (w : List ℤ) : List ℤ := (w.map fun l => -l).reverse

@[expose] def commW (u v : List ℤ) : List ℤ := u ++ v ++ invW u ++ invW v

@[expose] def prodP (n : ℕ) (l : List (Array ℕ)) : Array ℕ := l.foldr (pcomp n) (pid n)

@[expose] def powP (n : ℕ) (a : Array ℕ) (m : ℕ) : Array ℕ := prodP n (List.replicate m a)

@[expose] def ord4P (n : ℕ) (y : Array ℕ) : Bool :=
  !(peq n (pcomp n y y) (pid n)) && peq n (pcomp n (pcomp n y y) (pcomp n y y)) (pid n)

@[expose] def isInvP (n : ℕ) (x : Array ℕ) : Bool :=
  !(peq n x (pid n)) && peq n (pcomp n x x) (pid n)

inductive T4Wit where
  | skip
  | ord4 (fs : List ℕ) (m : ℕ)
  | faith (f p : ℕ)
  | noInv (p : ℕ)
deriving Inhabited

@[expose] def rho4W (w : List ℤ) : Array ℕ :=
  pword 800 InvData.s4Perms (pinvs 800 InvData.s4Perms) w

@[expose] def poolT4 (pool : Array (List ℤ × List ℤ)) : Array (Array ℕ × Array ℕ) :=
  pool.map fun uv => (rho4W (commW uv.1 uv.2), rho4W (invW (commW uv.1 uv.2)))

@[expose] def zT4 (e : Array ℕ) (cc : Array ℕ × Array ℕ) : Array ℕ :=
  pcomp 800 (pcomp 800 e cc.1) (pcomp 800 e cc.2)

@[expose] def evalZT4 (T Ti : Array (Array ℕ)) (k : ℕ) (uv : List ℤ × List ℤ) (p : ℕ) : ℕ :=
  evalLift T Ti InvData.parRecs k (evalWordPt T Ti (commW uv.1 uv.2)
    (evalLift T Ti InvData.parRecs k (evalWordPt T Ti (invW (commW uv.1 uv.2)) p)))

@[expose] def t4WitOK (T Ti E : Array (Array ℕ)) (pool : Array (List ℤ × List ℤ))
    (cs : Array (Array ℕ × Array ℕ)) (k : ℕ) : T4Wit → Bool
  | .skip => !(isInvP 800 E[k]!)
  | .ord4 fs m => fs.all (fun f => decide (f < cs.size)) &&
      ord4P 800 (powP 800 (prodP 800 (fs.map fun f => zT4 E[k]! cs[f]!)) m)
  | .faith f p => decide (f < pool.size) && decide (p < hnsData.n) &&
      peq 800 (pcomp 800 (zT4 E[k]! cs[f]!) (zT4 E[k]! cs[f]!)) (pid 800) &&
      evalZT4 T Ti k pool[f]! (evalZT4 T Ti k pool[f]! p) != p
  | .noInv p => decide (p < hnsData.n) &&
      evalLift T Ti InvData.parRecs k (evalLift T Ti InvData.parRecs k p) != p

@[noinline, expose] def t4Loop (T Ti E : Array (Array ℕ)) (pool : Array (List ℤ × List ℤ))
    (cs : Array (Array ℕ × Array ℕ)) (wits : Array T4Wit) : Bool :=
  allBelowN 16384 fun k => t4WitOK T Ti E pool cs k wits[k]!

@[noinline, expose] def t4Run (T : Array (Array ℕ)) (pool : Array (List ℤ × List ℤ))
    (wits : Array T4Wit) : Bool :=
  t4Loop T (pinvs hnsData.n T) pE pool (poolT4 pool) wits

@[noinline, expose] def hnT4Check (pool : Array (List ℤ × List ℤ)) (wits : Array T4Wit) : Bool :=
  pool.all (fun uv => plettersOK 10 uv.1 && plettersOK 10 uv.2) && wits.size == 16384 &&
    t4Run gTabs pool wits

inductive AWit where
  | skip
  | ord4 (fs : List ℕ) (m : ℕ)
deriving Inhabited

@[expose] def regsFrom (n : ℕ) (R : Array (Array ℕ)) : List (ℕ × ℕ) → Array (Array ℕ)
  | [] => R
  | ij :: rest => regsFrom n (R.push (compA n R[ij.1]! R[ij.2]!)) rest

@[expose] def progOK : ℕ → List (ℕ × ℕ) → Bool
  | _, [] => true
  | m, ij :: rest => decide (ij.1 < m) && decide (ij.2 < m) && progOK (m + 1) rest

@[expose] def regsA (n : ℕ) (S : Array (Array ℕ)) (prog : List (ℕ × ℕ)) : Array (Array ℕ) :=
  regsFrom n (S ++ S.map (invCand n)) prog

@[expose] def prodA (n : ℕ) (l : List (Array ℕ)) : Array ℕ := l.foldr (compA n) (idA n)

@[expose] def powA (n : ℕ) (a : Array ℕ) (m : ℕ) : Array ℕ := prodA n (List.replicate m a)

@[expose] def ord4A (n : ℕ) (y : Array ℕ) : Bool :=
  !(eqA n (compA n y y) (idA n)) && eqA n (compA n (compA n y y) (compA n y y)) (idA n)

@[expose] def isInvolA (n : ℕ) (x : Array ℕ) : Bool :=
  !(eqA n x (idA n)) && eqA n (compA n x x) (idA n)

@[expose] def aWitOK (n : ℕ) (cs : Array (Array ℕ)) (x : Array ℕ) : AWit → Bool
  | .skip => !(isInvolA n x)
  | .ord4 fs m => fs.all (fun f => decide (f < cs.size)) &&
      ord4A n (powA n (prodA n (fs.map fun f => commutatorA n x cs[f]!)) m)

@[noinline, expose] def aLoop (n N : ℕ) (cs pts : Array (Array ℕ)) (wits : Array AWit) : Bool :=
  allLt N fun i => aWitOK n cs pts[i]! wits[i]!

@[noinline, expose] def aCheck (n : ℕ) (S : Array (Array ℕ)) (prog : List (ℕ × ℕ))
    (pregs : List ℕ) (pool : Array (ℕ × ℕ)) (ps : List ℕ) (N : ℕ) (wits : Array AWit) : Bool :=
  let R := regsA n S prog
  let gs := (pregs.map fun i => R[i]!).toArray
  let cP := enumBfs n gs ps (2 * N)
  let cs := pool.map fun gh => commutatorA n R[gh.1]! R[gh.2]!
  allLt S.size (fun s => validA n S[s]!) && progOK (2 * S.size) prog &&
    pregs.all (fun i => decide (i < R.size)) &&
    pool.all (fun gh => decide (gh.1 < R.size) && decide (gh.2 < R.size) &&
      validA n R[gh.1]! && validA n R[gh.2]!) &&
    allLt cs.size (fun f => validA n cs[f]!) && ps.all (fun p => decide (p < n)) &&
    enumOK n gs ps cP && cP.pts.size == N && wits.size == N && aLoop n N cs cP.pts wits

@[expose] def psA : List ℕ := [0, 997, 1994, 2991, 3988, 4985, 5982, 6979, 7976]

@[expose] def hnACheck (prog : List (ℕ × ℕ)) (pregs : List ℕ) (pool : Array (ℕ × ℕ))
    (wits : Array AWit) : Bool :=
  aCheck InvData.f6Arr.size InvData.s6Perms prog pregs pool psA 1024 wits

@[expose] def parseNatsHN (s : String) : Array ℕ :=
  ((s.splitOn " ").filterMap String.toNat?).toArray

@[expose] def decodePoolT4 (s : String) : Array (List ℤ × List ℤ) := Id.run do
  let a := parseNatsHN s
  let mut out : Array (List ℤ × List ℤ) := #[]
  let mut i := 0
  for _ in [0:a.size] do
    if i < a.size then
      let l1 := a[i]!
      let u := ((a.extract (i + 1) (i + 1 + l1)).toList.map fun x => (x : ℤ) - 11)
      let l2 := a[i + 1 + l1]!
      let v := ((a.extract (i + 2 + l1) (i + 2 + l1 + l2)).toList.map fun x => (x : ℤ) - 11)
      out := out.push (u, v)
      i := i + 2 + l1 + l2
  return out

@[expose] def decodeT4 (s : String) : Array T4Wit := Id.run do
  let a := parseNatsHN s
  let mut out : Array T4Wit := #[]
  let mut i := 0
  for _ in [0:a.size] do
    if i < a.size then
      let c := a[i]!
      if c == 0 then
        out := out.push .skip; i := i + 1
      else if c == 1 then
        let l := a[i + 1]!
        out := out.push (.ord4 (a.extract (i + 2) (i + 2 + l)).toList a[i + 2 + l]!)
        i := i + 3 + l
      else if c == 2 then
        out := out.push (.faith a[i + 1]! a[i + 2]!); i := i + 3
      else
        out := out.push (.noInv a[i + 1]!); i := i + 2
  return out

@[expose] def decodePairs (s : String) : List (ℕ × ℕ) := Id.run do
  let a := parseNatsHN s
  let mut out : Array (ℕ × ℕ) := #[]
  for j in [0:a.size / 2] do
    out := out.push (a[2 * j]!, a[2 * j + 1]!)
  return out.toList

@[expose] def decodeA (s : String) : Array AWit := Id.run do
  let a := parseNatsHN s
  let mut out : Array AWit := #[]
  let mut i := 0
  for _ in [0:a.size] do
    if i < a.size then
      let c := a[i]!
      if c == 0 then
        out := out.push .skip; i := i + 1
      else
        let l := a[i + 1]!
        out := out.push (.ord4 (a.extract (i + 2) (i + 2 + l)).toList a[i + 2 + l]!)
        i := i + 3 + l
  return out

end CFSG.ComponentClassification.RankTwoSporadic.HN
