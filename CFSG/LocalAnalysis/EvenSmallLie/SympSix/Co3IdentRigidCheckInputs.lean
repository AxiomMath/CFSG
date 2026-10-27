module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentCube
public meta import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentCube
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.Co3Schreier.Basic

public section

namespace CFSG.EvenSmallLie.SympSix.Co3Ident

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Co3
  CFSG.Sporadic.Schreier.Co3.Native

@[expose] def zcA (t : Array ℕ) : ℕ :=
  if eqA 276 t (idA 276) then 0 else if eqA 276 t (genArr 4) then 1 else
    if eqA 276 t (genArr 0) then 2 else if eqA 276 t eaArr then 3 else 4

@[expose] def swapZ (k : ℕ) : ℕ := if k = 1 then 2 else if k = 2 then 1 else k

@[expose] def powA (t : Array ℕ) : ℕ → Array ℕ
  | 0 => idA 276
  | n + 1 => compA 276 (powA t n) t

@[expose] def expProf (t : Array ℕ) : List ℕ :=
  (List.range 24).map fun m => swapZ (zcA (powA t (m + 1)))

@[expose] def profOK (t : Array ℕ) : Array ℕ → List ℕ → Bool
  | _, [] => true
  | acc, e :: es => zcA (compA 276 acc t) == e && profOK t (compA 276 acc t) es

@[expose] def testsOK (Y : Array (Array ℕ)) (wsE : List (List ℕ × List ℕ)) : Bool :=
  wsE.all fun p => profOK (prodA 276 Y p.1) (idA 276) p.2

@[expose] def wordsOfLen (k : ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | n + 1 => (wordsOfLen k n).flatMap fun w => (List.range k).map fun i => w ++ [i]

@[expose] def testWords (k L : ℕ) : List (List ℕ) :=
  ((List.range L).flatMap fun n => wordsOfLen k (n + 1)).filter fun w => w.contains (k - 1)

@[expose] def withProf (ws : List (List ℕ)) : List (List ℕ × List ℕ) :=
  ws.map fun w => (w, expProf (prodA 276 gArrs w))

@[expose] def wsE1 : List (List ℕ × List ℕ) := withProf (testWords 1 1)
@[expose] def wsE2 : List (List ℕ × List ℕ) := withProf (testWords 2 4)
@[expose] def wsE3 : List (List ℕ × List ℕ) := withProf (testWords 3 3)

@[expose] def anyLt (n : ℕ) (p : ℕ → Bool) : Bool := (List.range n).any p

@[expose] def classData : Array ℕ × Array ℕ × Array ℕ := Id.run do
  let mut reps : Array ℕ := #[]
  let mut ck : Array ℕ := Array.replicate 4608 0
  let mut ci : Array ℕ := Array.replicate 4608 0
  let mut done : Array Bool := Array.replicate 4608 false
  for j in [0:4608] do
    if !done[j]! && testsOK #[hList[j]!] wsE1 then
      let k := reps.size
      reps := reps.push j
      done := done.set! j true
      ck := ck.set! j k
      let mut queue : Array (ℕ × Array ℕ) := #[(j, idA 276)]
      let mut q := 0
      for _ in [0:4608] do
        if q < queue.size then
          let pc := queue[q]!
          q := q + 1
          for i in [0:3] do
            let g := gArrs[i]!
            let p' := compA 276 g (compA 276 hList[pc.1]! (invCand 276 g))
            let ip := hIdx p'
            if ip < 4608 && !done[ip]! then
              done := done.set! ip true
              let c' := compA 276 g pc.2
              ck := ck.set! ip k
              ci := ci.set! ip (hIdx (invCand 276 c'))
              queue := queue.push (ip, c')
  return (reps, ck, ci)

@[expose] def psiGArrs : Array (Array ℕ) :=
  gArrs.map fun g => compA 276 (genArr 3) (compA 276 g (genArr 3))

@[expose] def psiFormOK (Y : Array (Array ℕ)) : Bool :=
  anyLt 4608 fun i => allLt 3 fun m =>
    eqA 276 (compA 276 hList[i]! psiGArrs[m]!) (compA 276 Y[m]! hList[i]!)

@[expose] def sigmaTab (Y : Array (Array ℕ)) : Array (Array ℕ) := Id.run do
  let mut T : Array (Array ℕ) := #[idA 276]
  for j in [1:4608] do
    T := T.push (compA 276 T[hPar[j]!]! Y[hLab[j]!]!)
  return T

@[expose] def chainBad (T : Array (Array ℕ)) (h hi : Array ℕ) (j₀ k : ℕ) : Bool :=
  let i1 := hIdx (compA 276 h (compA 276 hList[j₀]! hi))
  let x1 := compA 276 bcbArr (compA 276 T[i1]! bcbArr)
  let i1' := hIdx x1
  let i2 := hIdx (compA 276 h (compA 276 hList[i1']! hi))
  let x2 := compA 276 bcbArr (compA 276 T[i2]! bcbArr)
  let i2' := hIdx x2
  let i3 := hIdx (compA 276 h (compA 276 hList[i2']! hi))
  let x3 := compA 276 bcbArr (compA 276 T[i3]! bcbArr)
  decide (i1 < 4608) && decide (i1' < 4608) && decide (i2 < 4608) && decide (i2' < 4608) &&
    decide (i3 < 4608) &&
    eqA 276 (compA 276 hList[i1]! h) (compA 276 h hList[j₀]!) && eqA 276 hList[i1']! x1 &&
    eqA 276 (compA 276 hList[i2]! h) (compA 276 h hList[i1']!) && eqA 276 hList[i2']! x2 &&
    eqA 276 (compA 276 hList[i3]! h) (compA 276 h hList[i2']!) &&
    !eqA 276 (compA 276 x3 hList[k]!) (compA 276 hList[k]! hList[j₀]!)

@[expose] def planeBadOK (Y : Array (Array ℕ)) : Bool :=
  let T := sigmaTab Y
  treeTabOK 276 Y hPar hLab T 4608 &&
    anyLt 4608 fun jh =>
      let h := hList[jh]!
      let hi := invCand 276 h
      let iy := hIdx (compA 276 h (compA 276 yArr hi))
      decide (iy < 4608) && eqA 276 (compA 276 hList[iy]! h) (compA 276 h yArr) &&
        eqA 276 T[iy]! yArr &&
        allLt 4608 fun k => !commutesA 276 hList[k]! yArr ||
          anyLt 4608 fun j₀ => commutesA 276 hList[j₀]! yArr && chainBad T h hi j₀ k

@[expose] def leafOK (Y : Array (Array ℕ)) : Bool := psiFormOK Y || planeBadOK Y

@[expose] def e3Check : Bool :=
  let cd := classData
  (allLt cd.1.size fun k => decide (cd.1[k]! < 4608)) &&
  (allLt 4608 fun j => !testsOK #[hList[j]!] wsE1 ||
    (decide (cd.2.1[j]! < cd.1.size) && decide (cd.2.2[j]! < 4608) &&
      eqA 276 (compA 276 hList[cd.2.2[j]!]! hList[j]!)
        (compA 276 hList[cd.1[cd.2.1[j]!]!]! hList[cd.2.2[j]!]!))) &&
  (allLt cd.1.size fun k => allLt 4608 fun j₂ =>
    !testsOK #[hList[cd.1[k]!]!, hList[j₂]!] wsE2 || allLt 4608 fun j₃ =>
      !testsOK #[hList[cd.1[k]!]!, hList[j₂]!, hList[j₃]!] wsE3 ||
        leafOK #[hList[cd.1[k]!]!, hList[j₂]!, hList[j₃]!])

end CFSG.EvenSmallLie.SympSix.Co3Ident
