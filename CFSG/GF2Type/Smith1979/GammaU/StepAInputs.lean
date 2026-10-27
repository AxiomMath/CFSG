module

public import CFSG.GF2Type.Smith1979.GammaU.Lagr
public import CFSG.GF2Type.Smith1979.GammaU.Closure
public import CFSG.GF2Type.Smith1979.GammaU.Extend

public section

namespace CFSG.GF2Type.Smith1979.GammaU.StepA

open CFSG.GF2Type.Smith1979.GammaU

@[expose] def a0 : ℕ := 3072

@[expose] def gamuGens : List (Array ℕ) :=
  [#[1, 2, 32, 8, 16, 4, 64, 128, 2048, 512, 1024, 256],
    #[2, 4, 1112, 1097, 32, 25, 128, 256, 593, 1553, 2048, 1600],
    #[64, 2, 4, 8, 16, 32, 65, 128, 256, 512, 1024, 2048],
    #[1, 2, 4, 8, 16, 32, 65, 130, 260, 520, 1040, 2080]]

@[expose] def saGens : List (Array ℕ) :=
  [#[952, 269, 3463, 3833, 2201, 1193, 3638, 841, 497, 3650, 1659, 2683],
    #[3778, 3961, 444, 3270, 413, 429, 3707, 317, 3718, 3443, 1734, 2758]]

@[expose] def dReps : List (List ℕ) :=
  [[960, 48, 9, 5, 3, 3072],
    [961, 48, 9, 5, 3, 3072],
    [1072, 960, 9, 5, 3, 3072],
    [1072, 961, 9, 5, 3, 3072],
    [768, 192, 48, 12, 3, 3072],
    [1072, 768, 192, 12, 3, 3072]]

@[expose] def d0 : List ℕ := [961, 48, 9, 5, 3, 3072]

@[expose] def ws : List ℕ := [3072, 1, 2, 4, 8, 16]

@[expose] def coefW : List ℕ := [4, 16, 64, 256, 1024, 1027, 8, 32, 128, 512, 2048, 2049]

@[expose] def k0 : Array ℕ := #[1, 2, 4, 8, 32, 16, 64, 128, 256, 512, 2048, 1024]

@[expose] def cBasis : List (Array ℕ) :=
  [#[1, 2, 3076, 3080, 796, 812, 64, 128, 3376, 3632, 1036, 2060],
    #[1, 3074, 4, 3080, 666, 682, 64, 3248, 256, 3632, 1034, 2058],
    #[3073, 2, 4, 3080, 601, 617, 3184, 128, 256, 3632, 1033, 2057],
    #[49, 50, 52, 3128, 535, 551, 3136, 3200, 3328, 560, 1992, 3016],
    #[14, 13, 11, 7, 1040, 2080, 910, 845, 715, 455, 1024, 2048]]

@[expose] def idR : Array ℕ := #[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

@[expose] def mulR (g h : Array ℕ) : Array ℕ := h.map (appN g)

@[expose] def isoN (r : Array ℕ) : Bool :=
  r.size == 12 && r.all (· < 4096) && (List.range 4096).all fun n => q0b (appN r n) == q0b n

@[expose] def unitaryN (r : Array ℕ) : Bool :=
  (List.range 12).all fun j => appN r (theta0N (2 ^ j)) == theta0N (appN r (2 ^ j))

@[expose] def antiN (r : Array ℕ) : Bool :=
  (List.range 12).all fun j => appN r (theta0N (2 ^ j)) == theta0N (theta0N (appN r (2 ^ j)))

@[expose] def gammaUN (r : Array ℕ) : Bool := isoN r && (unitaryN r || antiN r)

@[expose] def singClosure (_ : Unit := ()) : List ℕ :=
  bfsClosure id (gamuGens.map appN) 4096 [a0] ((∅ : Std.HashSet ℕ).insert a0) []

@[expose] def transOK (_ : Unit := ()) : Bool :=
  let C := singClosure ()
  (List.range 4096).all fun n => n == 0 || q0b n || C.contains n

@[expose] def gensOK (_ : Unit := ()) : Bool :=
  gamuGens.all gammaUN && saGens.all fun r => gammaUN r && appN r a0 == a0

@[expose] def keyD (s : List ℕ) : List ℕ := (spanList s).mergeSort (· ≤ ·)

@[expose] def closureD (rep : List ℕ) : List (List ℕ) :=
  bfsClosure keyD (saGens.map fun r s => s.map (appN r)) 5000 [rep]
    ((∅ : Std.HashSet (List ℕ)).insert (keyD rep)) []

@[expose] def coverOK (_ : Unit := ()) : Bool :=
  let K := dReps.map fun rep => (closureD rep).map keyD
  (lagrDFS 5 [a0] (lagrCand a0)).all fun v =>
    let kv := keyD v
    K.any fun ks => ks.contains kv

@[expose] def thetaPow (e y : ℕ) : ℕ := if e = 1 then theta0N y else theta0N (theta0N y)

@[expose] def u0 : ℕ := 1024

@[expose] def perp5 (e : ℕ) : List ℕ :=
  (List.range 4096).filter fun n =>
    !f0b n a0 && f0b n (theta0N a0) == (e == 2 && f0b ws[5]! a0)

@[expose] def candT (S P : List ℕ) (e : ℕ) (pre : List ℕ) : List ℕ :=
  let i := pre.length
  let w := ws[i]!
  let allowed : List ℕ :=
    if i = 0 then [a0] else if i ≤ 4 then S.map (w ^^^ ·) else P.map (w ^^^ ·)
  allowed.filter fun y =>
    q0b y == q0b w && f0b y (thetaPow e y) == f0b w (theta0N w) &&
      (i == 0 || 5 ≤ i || S.contains (thetaPow e y ^^^ theta0N w)) &&
      (List.range i).all fun j =>
        f0b y pre[j]! == f0b w ws[j]! &&
          f0b y (thetaPow e pre[j]!) == f0b w (theta0N ws[j]!) &&
          f0b (thetaPow e y) pre[j]! == f0b (theta0N w) ws[j]! &&
          f0b (thetaPow e y) (thetaPow e pre[j]!) == f0b (theta0N w) (theta0N ws[j]!)

@[expose] def imgsOf (e : ℕ) (ys : List ℕ) : List ℕ := ys.flatMap fun y => [y, thetaPow e y]

@[expose] def xorSel (c : ℕ) (imgs : List ℕ) : ℕ :=
  (List.range 12).foldl (fun acc k => if c.testBit k then acc ^^^ imgs[k]! else acc) 0

@[expose] def rowsOfImgs (imgs : List ℕ) : Array ℕ := (coefW.map fun c => xorSel c imgs).toArray

@[expose] def leafOK (D S : List ℕ) (r : Array ℕ) : Bool :=
  D.all (fun d => appN r d ^^^ d == 0 || appN r d ^^^ d == a0) && S.contains (appN r u0 ^^^ u0)

@[expose] def tdList (D : List ℕ) : List (Array ℕ) :=
  let S := spanList D
  [1, 2].flatMap fun e =>
    let P := perp5 e
    (extDFS (candT S P e) 6 []).filterMap fun ys =>
      let r := rowsOfImgs (imgsOf e ys)
      if leafOK D S r then some r else none

@[expose] def badOK (D : List ℕ) : Bool :=
  ((tdList D).map fun r => D.map (appN r)).dedup.length < 32

@[expose] def subsetProducts (gens : List (Array ℕ)) : List (Array ℕ) :=
  gens.foldl (fun acc g => acc ++ acc.map (mulR g)) [idR]

@[expose] def compOf (c : ℕ) : List (Array ℕ) :=
  subsetProducts ((List.range 5).map fun i =>
    if c.testBit i then mulR k0 cBasis[i]! else cBasis[i]!)

@[expose] def compOK (_ : Unit := ()) : Bool :=
  let T := tdList d0
  let S := spanList d0
  T.length == 64 && T.all (fun r => r.size == 12 && r.all (· < 4096)) && T.contains k0 &&
    gammaUN k0 && mulR k0 k0 == idR && appN k0 a0 == a0 && d0.all (fun d => appN k0 d == d) &&
    (List.range 4096).all (fun n => f0b n a0 || S.contains (appN k0 n ^^^ n)) &&
    cBasis.all T.contains &&
    (List.range 32).all fun c =>
      let C := compOf c
      C.dedup.length == 32 && C.all T.contains && !C.contains k0 &&
        C.all fun x => C.all fun y => C.contains (mulR x y)

@[expose] def stepAOrbitCheck (_ : Unit := ()) : Bool := transOK () && gensOK () && coverOK ()

@[expose] def stepATCheck (_ : Unit := ()) : Bool :=
  (dReps.all fun D => D == d0 || badOK D) && compOK ()

end CFSG.GF2Type.Smith1979.GammaU.StepA
