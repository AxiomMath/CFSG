module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.CoverCheck

public section

namespace CFSG.EvenSporadicStandard.TwoSuz

@[expose] def sylowText : String := include_str "SylowWords.txt"

@[expose] def jText : String := include_str "JWords.txt"

@[expose] def parseNats (s : String) : List ℕ := (s.splitOn " ").filterMap String.toNat?

@[expose] def parseLetters (s : String) : List ℕ :=
  ((s.splitOn " ").filter fun p => p ≠ "").flatMap fun p =>
    match p.splitOn ":" with
    | [g, e] =>
      match g.toNat?, e.toInt? with
      | some g, some e =>
        if 0 ≤ e then List.replicate e.toNat (2 * g) else List.replicate (-e).toNat (2 * g + 1)
      | _, _ => []
    | _ => []

@[expose] def sylowLines : Array String := (sylowText.splitOn "\n").toArray

@[expose] def jLines : Array String := (jText.splitOn "\n").toArray

@[expose] def sylowNat (i : ℕ) : ℕ := (sylowLines.getD i "").toNat?.getD 0

@[expose] def ngS : ℕ := sylowNat 0

@[expose] def sGenWords : List (List ℕ) :=
  (List.range ngS).map fun i => (parseNats (sylowLines.getD (i + 1) "")).map (2 * ·)

@[expose] def wx1 : List ℕ := parseLetters (sylowLines.getD (ngS + 1) "")

@[expose] def wx2 : List ℕ := parseLetters (sylowLines.getD (ngS + 2) "")

@[expose] def wz : List ℕ := parseLetters (sylowLines.getD (ngS + 3) "")

@[expose] def noS : ℕ := sylowNat (ngS + 4)

@[expose] def orbRep (k : ℕ) : List ℕ := parseLetters (sylowLines.getD (ngS + 5 + 3 * k) "")

@[expose] def orbConj (k : ℕ) : List ℕ :=
  (parseNats (sylowLines.getD (ngS + 6 + 3 * k) "")).map (2 * ·)

@[expose] def orbTgt (k : ℕ) : ℕ := sylowNat (ngS + 7 + 3 * k)

@[expose] def treeText : String := include_str "SylowTree.txt"

@[expose] def treeLines : Array String := (treeText.splitOn "\n").toArray

@[expose] def treePar : Array (ℕ × ℕ) :=
  let xs := (parseNats (treeLines.getD 1 "")).toArray
  #[(0, 0)] ++ (Array.range ((xs.size) / 2)).map fun i => (xs.getD (2 * i) 0, xs.getD (2 * i + 1) 0)

@[expose] def jExtraWord : List ℕ := (parseNats (jLines.getD 1 "")).map (2 * ·)

@[expose] def nComm : ℕ := (jLines.getD 2 "").toNat?.getD 0

@[expose] def commU (j : ℕ) : List ℕ := parseLetters (jLines.getD (3 + 2 * j) "")

@[expose] def commV (j : ℕ) : List ℕ := parseLetters (jLines.getD (4 + 2 * j) "")

@[expose] def genInComm (i : ℕ) : List ℕ := parseLetters (jLines.getD (3 + 2 * nComm + i) "")

@[expose] def invM' (A : Mt) : Mt :=
  ((List.range 100).find? fun k => powM A (k + 1) == oneM).elim oneM fun k => powM A k

@[expose] def matA2 : Mt := mulM matA matA

@[expose] def matA3 : Mt := mulM matA2 matA

@[expose] def matB2 : Mt := mulM matB matB

@[expose] def abGS : GenSys :=
  ⟨#[matA, matA2, matA3, matB, matB2], #[matA3, matA2, matA, matB2, matB]⟩

@[expose] def jWords : List (List ℕ) := sGenWords ++ [jExtraWord]

@[expose] def jMats : Array Mt := (jWords.map fun w => abGS.eval w).toArray

@[expose] def jGS : GenSys := ⟨jMats, jMats.map invM'⟩

@[expose] def sMats : Array Mt := jMats.extract 0 ngS

@[expose] def x1M : Mt := jGS.eval wx1

@[expose] def x2M : Mt := jGS.eval wx2

@[expose] def zM : Mt := jGS.eval wz

@[expose] def invWord (w : List ℕ) : List ℕ :=
  (w.map fun c => if c % 2 = 0 then c + 1 else c - 1).reverse

@[expose] def buildE (gens : Array Mt) (par : Array (ℕ × ℕ)) : Array Mt := Id.run do
  let mut E : Array Mt := #[oneM]
  for i in [1:par.size] do
    E := E.push (mulM (E.getD (par.getD i (0, 0)).1 oneM) (gens.getD (par.getD i (0, 0)).2 oneM))
  return E

@[expose] def distinctGo : List Mt → Std.HashSet Mt → Bool
  | [], _ => true
  | a :: l, s => !s.contains a && distinctGo l (s.insert a)

@[expose] def distinctB (E : Array Mt) : Bool := distinctGo E.toList ∅

@[expose] def closedB (gens E : Array Mt) : Bool :=
  let S : Std.HashSet Mt := Std.HashSet.ofList E.toList
  E.all fun e => gens.all fun g => S.contains (mulM e g)

@[expose] def treeB (gens E : Array Mt) (par : Array (ℕ × ℕ)) : Bool :=
  E.size == par.size && E.getD 0 oneM == oneM && 0 < E.size &&
    (List.range E.size).all fun i =>
      i == 0 || ((par.getD i (0, 0)).1 < i && (par.getD i (0, 0)).2 < gens.size &&
        E.getD i oneM ==
          mulM (E.getD (par.getD i (0, 0)).1 oneM) (gens.getD (par.getD i (0, 0)).2 oneM))

@[expose] def sqCount (sqs : Array Mt) (c : Mt) : ℕ :=
  Nat.count (fun i => sqs.getD i oneM == c) sqs.size

@[expose] def conjGen (k : ℕ) (m : Mt) : Mt :=
  mulM (mulM (jGS.mats.getD k oneM) m) (jGS.invs.getD k oneM)

@[expose] def bfsOrbit (r : Mt) : Array Mt × Array (ℕ × ℕ) := Id.run do
  let mut elems : Array Mt := #[r]
  let mut par : Array (ℕ × ℕ) := #[(0, 0)]
  let mut seen : Std.HashSet Mt := (∅ : Std.HashSet Mt).insert r
  let mut i := 0
  while i < elems.size do
    for k in [0:ngS] do
      let m := conjGen k elems[i]!
      if !seen.contains m then
        seen := seen.insert m
        elems := elems.push m
        par := par.push (i, k)
    i := i + 1
  return (elems, par)

@[expose] def orbTreeB (r : Mt) (O : Array Mt) (par : Array (ℕ × ℕ)) : Bool :=
  O.size == par.size && O.getD 0 oneM == r && 0 < O.size &&
    (List.range O.size).all fun i =>
      i == 0 || ((par.getD i (0, 0)).1 < i && (par.getD i (0, 0)).2 < ngS &&
        O.getD i oneM == conjGen (par.getD i (0, 0)).2 (O.getD (par.getD i (0, 0)).1 oneM))

@[expose] def tgtM (i : ℕ) : Mt := if i = 1 then x1M else x2M

@[expose] def orbitB (k : ℕ) : Bool :=
  let r := jGS.eval (orbRep k)
  let g := abGS.eval (orbConj k)
  let ob := bfsOrbit r
  (orbTgt k == 1 || orbTgt k == 2) && mulM r g == mulM g (tgtM (orbTgt k)) &&
    orbTreeB r ob.1 ob.2

@[expose] def orbitSet : Std.HashSet Mt :=
  Std.HashSet.ofList ((List.range noS).flatMap fun k => (bfsOrbit (jGS.eval (orbRep k))).1.toList)

@[expose] def lettersLt (n : ℕ) (w : List ℕ) : Bool := w.all fun c => decide (c / 2 < n)

@[noinline, expose] def sylowCheck : Bool :=
  let par := treePar
  let E := buildE sMats par
  let sqs := E.map fun e => mulM e e
  abGS.valid && jGS.valid && ngS == 4 && jMats.size == 5 &&
    lettersLt 4 wx1 && lettersLt 4 wx2 && lettersLt 4 wz &&
    (List.range noS).all (fun k => lettersLt 4 (orbRep k)) &&
    treeB sMats E par && distinctB E && closedB sMats E && E.size == 16384 &&
    sqCount sqs zM == 1056 && sqCount sqs x1M == 384 && sqCount sqs x2M == 352 &&
    (List.range ngS).all (fun k => mulM (sMats.getD k oneM) x1M == mulM x1M (sMats.getD k oneM) &&
      mulM (sMats.getD k oneM) x2M == mulM x2M (sMats.getD k oneM) &&
      mulM (sMats.getD k oneM) zM == mulM zM (sMats.getD k oneM)) &&
    zM == negM && x2M == mulM zM x1M &&
    (List.range noS).all orbitB &&
    (List.range E.size).all fun i =>
      !(sqs.getD i oneM == oneM && E.getD i oneM != oneM && E.getD i oneM != zM) ||
        orbitSet.contains (E.getD i oneM)

@[expose] def commUM (j : ℕ) : Mt := jGS.eval (commU j)

@[expose] def commVM (j : ℕ) : Mt := jGS.eval (commV j)

@[expose] def commM (j : ℕ) : Mt :=
  jGS.eval (commU j ++ commV j ++ invWord (commU j) ++ invWord (commV j))

@[expose] def commInvM (j : ℕ) : Mt :=
  jGS.eval (commV j ++ commU j ++ invWord (commV j) ++ invWord (commU j))

@[expose] def cGS : GenSys := ⟨((List.range nComm).map commM).toArray,
  ((List.range nComm).map commInvM).toArray⟩

@[noinline, expose] def jCheck : Bool :=
  abGS.valid && jGS.valid && cGS.valid && nComm == 2 && ngS == 4 &&
    (List.range 5).all (fun i => cGS.eval (genInComm i) == jMats.getD i oneM) &&
    (List.range 5).all (fun i => mulM (jMats.getD i oneM) x1M == mulM x1M (jMats.getD i oneM) &&
      mulM (jMats.getD i oneM) x2M == mulM x2M (jMats.getD i oneM))

end CFSG.EvenSporadicStandard.TwoSuz

