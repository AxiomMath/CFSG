module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.SzCoverNative

public section

namespace CFSG.EvenSporadicStandard.TwoRu.CentCover

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Presentation.Ru.Exact
  CFSG.Sporadic.Bridge.SurjD.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Tits
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.LieType.Multipliers.Tits
  CFSG.Sporadic.Recognition.RuMultiplier CFSG.Sporadic.RuSchreier CFSG.Quasithin.KGC31.RuCover
  CFSG.EvenSporadicStandard.TwoRu.SzCover

@[expose] def invW (w : List ℤ) : List ℤ := w.reverse.map fun l => -l

@[expose] def commW (u v : List ℤ) : List ℤ := u ++ v ++ invW u ++ invW v

@[expose] def jW (k : ℕ) : List ℤ := ruJWords.getD k []

@[expose] def fW : ℕ → List ℤ
  | 0 => jW 4 ++ jW 4
  | 1 => commW (jW 0) (jW 1)
  | 2 => commW (jW 0) (jW 2)
  | 3 => commW (jW 0) (jW 3)
  | 4 => commW (jW 0) (jW 5)
  | 5 => commW (jW 1) (jW 2)
  | _ => []

@[expose] def etaW (m c : ℕ) : List ℤ :=
  (List.range m).foldl (fun acc j => if c.testBit j then acc ++ fW j else acc) []

@[expose] def gIdx : List ℕ := [0, 1, 2, 5]

@[expose] def gWm (m s : ℕ) : List ℤ :=
  (List.range m).foldl (fun acc b => if s.testBit b then acc ++ jW (gIdx.getD b 0) else acc) []

@[expose] def gW (s : ℕ) : List ℤ := gWm 4 s

@[expose] def y2W : List ℤ := jW 0 ++ jW 2 ++ jW 3

@[expose] def zW : List ℤ := List.replicate 10 1

@[expose] def y5W : List ℤ := [1, 2, -1, -1, -1, 2]

@[expose] def facTerms : ℕ → List (List ℤ × Bool)
  | 0 => [([1, 2], true), ([-1, -2, -1], false), ([1, 2, 1, -2], false), ([-2, 1, 2], true)]
  | 1 => [([1, 2], true), ([-1, -2, -1], false), ([1, 2, -1, 2, -1], false),
      ([1, -2, 1, -2], true)]
  | 2 => [([1, 2], true), ([-1, -2, -1], false), ([], true), ([1, 2, 1, 1, -2], false)]
  | 3 => [([1, 2], true), ([-1, -2, -1], false), ([1, 1, 1, 1, 1], true),
      ([1, -2, 1, 1, 2], false)]
  | 4 => [([-1, -1, 2, 1], true), ([-1, -2, -1, -1], false), ([1, 1, 1, 2], false),
      ([1, 2, -1, 2, 2], true)]
  | 5 => [([1, 2], true), ([-1, -2, -1], false), ([2, 1, -2], true), ([1, 1, 2, 1, -2], false)]
  | _ => []

@[expose] def termW (t : List ℤ × Bool) : List ℤ :=
  t.1 ++ (if t.2 then y5W else invW y5W) ++ invW t.1

@[expose] def facW (k : ℕ) : List ℤ := ((facTerms k).map termW).flatten

@[expose] def ccEqB (n : ℕ) (S Sinv : Array (Array ℕ)) (u v : List ℤ) : Bool :=
  lettersOK 2 u && lettersOK 2 v && eqA n (wordA n S Sinv u) (wordA n S Sinv v)

@[expose] def ccNeB (n : ℕ) (S Sinv : Array (Array ℕ)) (u v : List ℤ) : Bool :=
  lettersOK 2 u && lettersOK 2 v && !eqA n (wordA n S Sinv u) (wordA n S Sinv v)

@[expose] def ccEtaTab (n : ℕ) (S Sinv : Array (Array ℕ)) : List (ℕ × Array ℕ) :=
  (List.range 64).map fun c => (c, wordA n S Sinv (etaW 6 c))

@[expose] def ccInEta (n : ℕ) (E : List (ℕ × Array ℕ)) (T : Array ℕ) : Bool :=
  E.any fun p => eqA n T p.2

@[expose] def ccWordInEta (n : ℕ) (S Sinv : Array (Array ℕ)) (E : List (ℕ × Array ℕ))
    (w : List ℤ) : Bool :=
  lettersOK 2 w && ccInEta n E (wordA n S Sinv w)

@[expose] def ccBase (n : ℕ) (S Sinv : Array (Array ℕ)) : Bool :=
  ccEqB n S Sinv (zW ++ zW) [] && ccEqB n S Sinv ([2] ++ zW) (zW ++ [2]) &&
    ccEqB n S Sinv (y5W ++ y5W ++ y5W ++ y5W ++ y5W) [] && ccNeB n S Sinv y5W []

@[expose] def ccFac (n : ℕ) (S Sinv : Array (Array ℕ)) : Bool :=
  (List.range 6).all fun k =>
    ccEqB n S Sinv (facW k) (jW k) && (facTerms k).all fun t => lettersOK 2 t.1

@[expose] def ccElem (n : ℕ) (S Sinv : Array (Array ℕ)) : Bool :=
  (List.range 6).all (fun i => ccEqB n S Sinv (fW i ++ fW i) []) &&
    (List.range 6).all fun i => (List.range 6).all fun j =>
      ccEqB n S Sinv (fW i ++ fW j) (fW j ++ fW i)

@[expose] def ccEta (n : ℕ) (S Sinv : Array (Array ℕ)) (E : List (ℕ × Array ℕ)) (T : Array ℕ) :
    Bool :=
  (List.range 64).all (fun c => lettersOK 2 (etaW 6 c)) &&
    E.all (fun p => p.1 == 0 || !eqA n p.2 (idA n)) &&
    (List.range 6).all (fun k => (List.range 6).all fun i =>
      ccWordInEta n S Sinv E (jW k ++ fW i ++ invW (jW k))) &&
    (List.range 6).all (fun a => ccWordInEta n S Sinv E (jW a ++ jW a)) &&
    (List.range 6).all (fun a => (List.range 6).all fun b =>
      ccWordInEta n S Sinv E (commW (jW a) (jW b))) &&
    ccWordInEta n S Sinv E zW && ccInEta n E T

@[expose] def ccCosets (n : ℕ) (S Sinv : Array (Array ℕ)) : Bool :=
  (List.range 16).all fun s => (List.range 16).all fun s' =>
    s == s' || (List.range 6).any fun i =>
      ccNeB n S Sinv (invW (gW s) ++ gW s' ++ fW i) (fW i ++ invW (gW s) ++ gW s')

@[expose] def ccY (n : ℕ) (S Sinv : Array (Array ℕ)) : Bool :=
  (List.range 6).all (fun i => ccEqB n S Sinv (jW 4 ++ fW i) (fW i ++ jW 4)) &&
    (List.range 6).all (fun i => ccEqB n S Sinv (y2W ++ fW i) (fW i ++ y2W)) &&
    ccEqB n S Sinv (commW (jW 4) y2W) zW

@[expose] def ccChkAt (n : ℕ) (t0 t1 : Array ℕ) : Bool :=
  let R := slotRunA n ruCProg t0 t1
  let S : Array (Array ℕ) := #[R.1, R.2.1]
  let Sinv : Array (Array ℕ) := #[invCand n R.1, invCand n R.2.1]
  let E := ccEtaTab n S Sinv
  szInvOK n t0 && szInvOK n t1 && R.2.2 && szInvOK n R.1 && szInvOK n R.2.1 &&
    ccBase n S Sinv && ccFac n S Sinv && ccElem n S Sinv && ccEta n S Sinv E (compA n t0 t0) &&
    ccCosets n S Sinv && ccY n S Sinv

@[expose] def ccChk (_ : Unit := ()) : Bool :=
  lettersOK gc (zword ruP1) && ccChkAt 16240 (p0A ()) (p1A ())

end CFSG.EvenSporadicStandard.TwoRu.CentCover
