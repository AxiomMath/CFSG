module

public import CFSG.Monster.B.Fischer.ArrCert

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43.Check

open CFSG.Monster.B.Fischer

@[expose] def reC (c : ℕ) : ℕ := c / 3 % 3

@[expose] def imC (c : ℕ) : ℕ := c % 3

@[expose] def mulC (c d : ℕ) : ℕ :=
  3 * ((reC c * reC d + 2 * (imC c * imC d)) % 3) + (reC c * imC d + imC c * reC d) % 3

@[expose] def addC (c d : ℕ) : ℕ := 3 * ((reC c + reC d) % 3) + (imC c + imC d) % 3

@[expose] def negC (c : ℕ) : ℕ := 3 * ((2 * reC c) % 3) + (2 * imC c) % 3

@[expose] def subC (c d : ℕ) : ℕ := addC c (negC d)

@[expose] def barC (c : ℕ) : ℕ := 3 * reC c + (2 * imC c) % 3

@[expose] def mulEntry (x y : Array ℕ) (sw : Bool) (i j : ℕ) : ℕ :=
  addC (addC (addC (mulC x[4 * i]! (if sw then barC y[j]! else y[j]!))
    (mulC x[4 * i + 1]! (if sw then barC y[4 + j]! else y[4 + j]!)))
    (mulC x[4 * i + 2]! (if sw then barC y[8 + j]! else y[8 + j]!)))
    (mulC x[4 * i + 3]! (if sw then barC y[12 + j]! else y[12 + j]!))

@[expose] def mulMat (x y : Array ℕ) (sw : Bool) : Array ℕ :=
  Array.ofFn (n := 16) fun k => mulEntry x y sw ((k : ℕ) / 4) ((k : ℕ) % 4)

@[expose] def mulRaw (x y : Array ℕ) : Array ℕ :=
  (mulMat x y (x[16]! == 1)).push ((x[16]! + y[16]!) % 2)

@[expose] def idMat : Array ℕ := #[3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 3]

@[expose] def idCode : Array ℕ := idMat.push 0

@[expose] def scal (c : ℕ) : Array ℕ := #[c, 0, 0, 0, 0, c, 0, 0, 0, 0, c, 0, 0, 0, 0, c, 0]

@[expose] def isZ (z : Array ℕ) : Bool :=
  z == scal 3 || z == scal 6 || z == scal 1 || z == scal 2

@[expose] def powRaw (x : Array ℕ) : ℕ → Array ℕ
  | 0 => idCode
  | n + 1 => mulRaw x (powRaw x n)

@[expose] def conjT (x : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 17) fun k =>
    if (k : ℕ) < 16 then barC x[4 * ((k : ℕ) % 4) + (k : ℕ) / 4]! else 0

@[expose] def rawValid (x : Array ℕ) : Bool :=
  x.size == 17 && (List.range 16).all (fun k => decide (x[k]! < 9)) && decide (x[16]! < 2) &&
    mulMat (conjT x) x false == idMat

@[expose] def firstNZ (x : Array ℕ) : ℕ :=
  (((List.range 16).map fun k => x[k]!).find? fun w => decide (w ≠ 0)).getD 0

@[expose] def mC : ℕ → ℕ
  | 1 => 2
  | 2 => 1
  | 3 => 3
  | 4 => 3
  | 5 => 1
  | 6 => 6
  | 7 => 2
  | 8 => 6
  | _ => 0

@[expose] def smulCode (c : ℕ) (x : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 17) fun k => if (k : ℕ) < 16 then mulC c x[(k : ℕ)]! else x[16]!

@[expose] def normalize (x : Array ℕ) : Array ℕ := smulCode (mC (firstNZ x)) x

@[expose] def eqZ (x y : Array ℕ) : Bool := normalize x == normalize y

@[expose] def valid (x : Array ℕ) : Bool := rawValid x && normalize x == x

@[expose] def keyOf (x : Array ℕ) : ℕ := Nat.ofDigits 9 x.toList

@[expose] def det3C (a b c d e f g h i : ℕ) : ℕ :=
  subC (addC (addC (mulC (mulC a e) i) (mulC (mulC b f) g)) (mulC (mulC c d) h))
    (addC (addC (mulC (mulC c e) g) (mulC (mulC a f) h)) (mulC (mulC b d) i))

@[expose] def detC (x : Array ℕ) : ℕ :=
  subC (addC (mulC x[0]! (det3C x[5]! x[6]! x[7]! x[9]! x[10]! x[11]! x[13]! x[14]! x[15]!))
      (mulC x[2]! (det3C x[4]! x[5]! x[7]! x[8]! x[9]! x[11]! x[12]! x[13]! x[15]!)))
    (addC (mulC x[1]! (det3C x[4]! x[6]! x[7]! x[8]! x[10]! x[11]! x[12]! x[14]! x[15]!))
      (mulC x[3]! (det3C x[4]! x[5]! x[6]! x[8]! x[9]! x[10]! x[12]! x[13]! x[14]!)))

structure Rep where
  x : Array ℕ
  t : Array ℕ
  g1 : Array ℕ
  g1i : Array ℕ
  g2 : Array ℕ
  g2i : Array ℕ
  wa : List (ℕ × ℕ)
  wb : List (ℕ × ℕ)
  ma : ℕ
  mb : ℕ
  j : ℕ
  deriving Inhabited

structure Data where
  gens : Array (Array ℕ)
  reps : Array Rep
  tab : Array (ℕ × ℕ)
  fuel : ℕ

@[expose] def pairUp : List ℕ → List (ℕ × ℕ)
  | a :: b :: rest => (a, b) :: pairUp rest
  | _ => []

@[expose] def tabOfString (s : String) : Array (ℕ × ℕ) :=
  (pairUp (((s.splitOn " ").filter (· ≠ "")).map String.toNat!)).toArray

@[expose] def act (gens : Array (Array ℕ)) (k : ℕ) (a : Array ℕ) : Array ℕ :=
  normalize (mulRaw gens[k]! a)

@[expose] def bfs (D : Data) : ArrCert := arrBfs (act D.gens) D.gens.size keyOf idCode D.fuel

@[expose] def sylowOK (D : Data) : Bool :=
  (List.range D.gens.size).all (fun k => rawValid D.gens[k]!) &&
    arrCertOK (act D.gens) D.gens.size valid keyOf idCode (bfs D) && (bfs D).pts.size == 1024

@[expose] def orderEight (p4 p8 : Array (Array ℕ)) : List ℕ :=
  (List.range p4.size).filter fun i => isZ p8[i]! && !isZ p4[i]!

@[expose] def involutions (pts p2 : Array (Array ℕ)) : List ℕ :=
  (List.range pts.size).filter fun j => isZ p2[j]! && !isZ pts[j]!

@[expose] def goodPairs (pts p2 p4 p8 : Array (Array ℕ)) : List (ℕ × ℕ) :=
  (orderEight p4 p8).flatMap fun i =>
    ((involutions pts p2).filter fun j =>
      eqZ (mulRaw pts[i]! pts[j]!) (mulRaw pts[j]! pts[i]!)).map fun j => (i, j)

@[expose] def squares (pts : Array (Array ℕ)) : Array (Array ℕ) := pts.map fun z => mulRaw z z

@[expose] def coverOK (D : Data) : Bool :=
  let pts := (bfs D).pts
  let p2 := squares pts
  let p4 := squares p2
  let p8 := squares p4
  let good := goodPairs pts p2 p4 p8
  good.length == D.tab.size &&
    (good.zip D.tab.toList).all fun e =>
      decide (e.2.1 < D.reps.size) && decide (e.2.2 < pts.size) &&
        eqZ (mulRaw pts[e.2.2]! pts[e.1.1]!) (mulRaw D.reps[e.2.1]!.x pts[e.2.2]!) &&
        eqZ (mulRaw pts[e.2.2]! pts[e.1.2]!) (mulRaw D.reps[e.2.1]!.t pts[e.2.2]!)

@[expose] def evalWord (ls : Array (Array ℕ)) (w : List (ℕ × ℕ)) : Array ℕ :=
  w.foldl (fun acc l => mulRaw acc (powRaw ls[l.1]! l.2)) idCode

@[expose] def repX1 (r : Rep) : Array ℕ := mulRaw (mulRaw r.g1 r.x) r.g1i

@[expose] def repX2 (r : Rep) : Array ℕ := mulRaw (mulRaw r.g2 r.x) r.g2i

@[expose] def repLetters (r : Rep) : Array (Array ℕ) := #[r.x, repX1 r, repX2 r]

@[expose] def repA (r : Rep) : Array ℕ := evalWord (repLetters r) r.wa

@[expose] def repB (r : Rep) : Array ℕ := evalWord (repLetters r) r.wb

@[expose] def repC (r : Rep) : Array ℕ := mulRaw (repA r) (repB r)

@[expose] def repOK (r : Rep) : Bool :=
  rawValid r.x && rawValid r.t && rawValid r.g1 && rawValid r.g1i && rawValid r.g2 &&
    rawValid r.g2i && r.g1[16]! == 0 && r.g2[16]! == 0 && detC r.g1 == 3 && detC r.g2 == 3 &&
    isZ (mulRaw r.g1 r.g1i) && isZ (mulRaw r.g2 r.g2i) &&
    eqZ (mulRaw r.g1 r.t) (mulRaw r.t r.g1) && eqZ (mulRaw r.g2 r.t) (mulRaw r.t r.g2) &&
    r.wa.all (fun l => decide (l.1 < 3)) && r.wb.all (fun l => decide (l.1 < 3)) &&
    decide (r.ma % 2 = 1) && isZ (powRaw (repA r) r.ma) && decide (r.mb % 2 = 1) &&
    isZ (powRaw (repB r) r.mb) && isZ (powRaw (powRaw (repC r) r.j) 2) &&
    !isZ (powRaw (repC r) r.j)

@[expose] def repsOK (D : Data) : Bool := D.reps.toList.all repOK

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43.Check
