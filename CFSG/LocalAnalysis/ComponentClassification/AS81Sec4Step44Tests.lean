module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Step44Data
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeSylowData
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeAutSylowTests
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HexaData

public section

namespace CFSG.ComponentClassification.AS81.Hexa

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.ComponentClassification.AS81.HeSylow

@[expose] def v0A (i : ℕ) : Array ℕ := hexaV0[i]!

@[expose] def inV0A (x : Array ℕ) : Bool := (List.range 4).any fun i => eqA 64 x (v0A i)

@[expose] def fix16A (m : Array ℕ) : Bool := (List.range 16).all fun v => m[v]! == v

@[expose] def normV0A (m : Array ℕ) : Bool := (List.range 4).all fun i => inV0A (conjA 64 m (v0A i))

@[expose] def k36Gens : List (Array ℕ) := hexaV0 ++ [hexaOmega, hexaMu]

@[expose] def sixTrivA (m : Array ℕ) : Bool :=
  [1, 2, 3].all (fun u => m[16 * u]! / 16 == u) &&
    (List.range 4).all fun j => eqA 64 (conjA 64 m (v0A j)) (v0A j)

@[expose] def v0Check : Bool :=
  let M := eltsN 64 hexaMGens
  let K := eltsN 64 k36Gens
  let W := eltsN 64 [hexaOmega, hexaMu]
  hexaV0.length == 4 && eqA 64 (v0A 0) (idA 64) &&
    (List.range 4).all (fun i => i == 0 || !(eqA 64 (v0A i) (idA 64))) &&
    (List.range 4).all (fun i => (List.range 4).all fun j =>
      eqA 64 (mulN 64 (v0A i) (v0A j)) (v0A (i ^^^ j))) &&
    (List.range 4).all (fun i => validA 64 (v0A i) && inLN 64 M (v0A i) && fix16A (v0A i)) &&
    M.all (fun m => !(fix16A m) || inV0A m) &&
    validA 64 hexaOmega && inLN 64 M hexaOmega &&
    (List.range 64).all (fun v => v == 0 || hexaOmega[v]! != v) &&
    eqA 64 (powN 64 hexaOmega 3) (idA 64) &&
    (List.range 4).all (fun i => commN 64 hexaOmega (v0A i)) &&
    validA 64 hexaMu && inLN 64 M hexaMu && eqA 64 (powN 64 hexaMu 3) (idA 64) &&
    commN 64 hexaMu hexaOmega &&
    hexaMuPi.size == 4 && (List.range 4).all (fun i => decide (hexaMuPi[i]! < 4) &&
      eqA 64 (conjA 64 hexaMu (v0A i)) (v0A hexaMuPi[i]!)) &&
    enumCheckN 64 k36Gens 36 && enumCheckN 64 [hexaOmega, hexaMu] 9 &&
    K.all (fun k => (List.range 4).any fun i => inLN 64 W (mulN 64 (v0A i) k)) &&
    K.all (fun k => inV0A (powN 64 k 9)) &&
    M.all (fun m => !(normV0A m && inV0A (powN 64 m 9)) || inLN 64 K m) &&
    (M.filter normV0A).length == 144 && enumCheckN 64 hexaNormGens 144 &&
    hexaNormGens.all (fun m => inLN 64 M m && normV0A m) &&
    M.all (fun m => !(normV0A m) || (List.range 16).all fun v => decide (m[v]! < 16)) &&
    M.all (fun m => !(normV0A m && sixTrivA m) || inV0A m)

@[expose] def smStar (i j : ℕ) : ℕ :=
  ((i % 64) ^^^ (v0A (i / 64))[j % 64]!) + 64 * ((i / 64) ^^^ (j / 64))

@[expose] def omuA (a b : ℕ) : Array ℕ :=
  mulN 64 (powN 64 hexaOmega (a % 3)) (powN 64 hexaMu (b % 3))

@[expose] def muPiN : ℕ → ℕ → ℕ
  | 0, m => m
  | b + 1, m => hexaMuPi[muPiN b m]!

@[expose] def smTau (a b i : ℕ) : ℕ := (omuA a b)[i % 64]! + 64 * muPiN (b % 3) (i / 64)

@[expose] def sigN (s1 s2 c : ℕ × ℕ) : ℕ × ℕ :=
  ((c.1 * s1.1 + c.2 * s2.1) % 3, (c.1 * s1.2 + c.2 * s2.2) % 3)

@[expose] def smComp (s1 s2 d : ℕ × ℕ) (y code : ℕ) : ℕ :=
  if code = 0 then 0 else
    smTau (sigN s1 s2 ((code - 1) * d.1, (code - 1) * d.2)).1
      (sigN s1 s2 ((code - 1) * d.1, (code - 1) * d.2)).2 y

@[expose] def smCandAt (s1 s2 : ℕ × ℕ) (y0 y1 y2 y3 i : ℕ) : ℕ :=
  smStar (smStar (smStar (smComp s1 s2 (0, 1) y0 hexaNF[4 * i]!)
    (smComp s1 s2 (1, 0) y1 hexaNF[4 * i + 1]!)) (smComp s1 s2 (0, 1) y2 hexaNF[4 * i + 2]!))
    (smComp s1 s2 (0, 1) y3 hexaNF[4 * i + 3]!)

@[expose] def smCand (s1 s2 : ℕ × ℕ) (y0 y1 y2 y3 : ℕ) : Array ℕ :=
  Array.ofFn fun i : Fin 256 => smCandAt s1 s2 y0 y1 y2 y3 i.val

@[expose] def smFix (s1 s2 k : ℕ × ℕ) : List ℕ :=
  (List.range 256).filter fun i => i != 0 && smTau (sigN s1 s2 k).1 (sigN s1 s2 k).2 i == i

@[expose] def smHomA (f : Array ℕ) : Bool :=
  (List.range 256).all fun i => (List.range 256).all fun j => f[smStar i j]! == smStar f[i]! f[j]!

@[expose] def f3Pairs : List (ℕ × ℕ) := (List.range 3).flatMap fun a => (List.range 3).map (a, ·)

@[expose] def smSigmas : List ((ℕ × ℕ) × (ℕ × ℕ)) :=
  f3Pairs.flatMap fun s1 => f3Pairs.filterMap fun s2 =>
    if (s1.1 * s2.2 + 2 * (s1.2 * s2.1)) % 3 == 0 then none else some (s1, s2)

@[expose] def smAutN (N : List (Array ℕ)) : Bool :=
  smSigmas.all fun s => (smFix s.1 s.2 (1, 0)).all fun y0 => (smFix s.1 s.2 (0, 1)).all fun y1 =>
    (smFix s.1 s.2 (1, 1)).all fun y2 => (smFix s.1 s.2 (1, 2)).all fun y3 =>
      !(smHomA (smCand s.1 s.2 y0 y1 y2 y3)) || inLN 256 N (smCand s.1 s.2 y0 y1 y2 y3)

@[expose] def presTA (f : Array ℕ) : Bool := (List.range 64).all fun i => decide (f[i]! < 64)

@[expose] def smLamA (x : ℕ) : Array ℕ := Array.ofFn fun i : Fin 256 => smStar x i.val

@[expose] def smLamGens : List (Array ℕ) := [1, 2, 4, 8, 16, 32, 64, 128].map smLamA

@[expose] def pairA (n : ℕ) (a b : Array ℕ) : Array ℕ := a ++ b.map (· + n)

@[expose] def smCheck : Bool :=
  let N := eltsN 256 hexaNGens
  let NE := eltsN 256 hexaNEGens
  f3Pairs.all (fun c => f3Pairs.all fun c' => (List.range 256).all fun i =>
      smTau c.1 c.2 (smTau c'.1 c'.2 i) == smTau (c.1 + c'.1) (c.2 + c'.2) i) &&
    f3Pairs.all (fun c => c == (0, 0) || (List.range 256).any fun i => smTau c.1 c.2 i != i) &&
    smTau 1 0 64 == 64 && smTau 0 1 30 == 30 && smTau 1 1 4 == 4 && smTau 1 2 1 == 1 &&
    eqA 256 (smCand (1, 0) (0, 1) 64 30 4 1) (idA 256) &&
    enumCheckN 256 hexaNGens 72 && hexaNGens.all smHomA && smAutN N &&
    enumCheckN 256 hexaNEGens 36 && hexaNEGens.all (inLN 256 N) &&
    N.all (fun f => !(presTA f) || inLN 256 NE f) &&
    enumCheckN 256 hexaPGens 8 && hexaPGens.all (inLN 256 N) &&
    enumCheckN 256 hexaPEGens 4 && hexaPEGens.all (inLN 256 NE) &&
    enumCheckN 256 smLamGens 256 &&
    enumCheckN 256 (smLamGens ++ hexaPGens) 2048 &&
    enumCheckN 288 (List.zipWith (pairA 256) (smLamGens ++ hexaPGens) hexaAbImgs) 2048 &&
    hexaAbImgs.length == 10 && (smLamGens ++ hexaPGens).all (·.size == 256) &&
    hexaAbImgs.all (·.size == 32) && enumCheckN 32 hexaAbImgs 2048 &&
    enumCheckN 32 GrSLit.HeldFix.hfT0Tabs32.toList 2048 &&
    GrSLit.HeldFix.hfT0Tabs32.toList.all (inLN 32 (eltsN 32 hexaAbImgs)) &&
    enumCheckN 256 (smLamGens ++ hexaPEGens) 1024 &&
    enumCheckN 272 (List.zipWith (pairA 256) (smLamGens ++ hexaPEGens) hexaAaImgs) 1024 &&
    hexaAaImgs.length == 10 && (smLamGens ++ hexaPEGens).all (·.size == 256) &&
    hexaAaImgs.all (·.size == 16) && enumCheckN 16 hexaAaImgs 1024 &&
    enumCheckN 16 heSyl16 1024 &&
    heSyl16.all (inLN 16 (eltsN 16 hexaAaImgs))

@[expose] def step44Check : Bool := v0Check && smCheck

end CFSG.ComponentClassification.AS81.Hexa
