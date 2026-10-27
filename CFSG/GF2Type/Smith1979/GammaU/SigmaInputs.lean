module

public import CFSG.GF2Type.Smith1979.GammaU.EnumDefs
public import CFSG.GF2Type.Smith1979.GammaU.ResidualPairInputs

public section

namespace CFSG.GF2Type.Smith1979.GammaU.SigmaP

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.GammaU.Enum
open CFSG.GF2Type.Smith1979.GammaU.ResPair

@[expose] def s45_0 : List ℕ :=
  [12, 48, 51, 63, 204, 207, 240, 252, 255, 768, 771, 780, 783, 819, 828, 831, 963, 972, 1008, 1011, 1020, 3072, 3084, 3120, 3123, 3135, 3264, 3267, 3276, 3279, 3315, 3324, 3327, 3843, 3855, 3888, 3891, 3903, 4032, 4035, 4044, 4047, 4083, 4092, 4095]

@[expose] def s45_1 : List ℕ :=
  [5, 48, 136, 184, 320, 325, 373, 461, 509, 522, 570, 575, 642, 647, 690, 695, 842, 890, 895, 1010, 1015, 3072, 3077, 3120, 3208, 3213, 3256, 3261, 3440, 3528, 3533, 3576, 3581, 3594, 3599, 3642, 3714, 3719, 3762, 3767, 3914, 3919, 3962, 4082, 4087]

@[expose] def s45 (i : ℕ) : List ℕ := if i = 0 then s45_0 else s45_1

@[expose] def sigmaBasis (i : ℕ) : List ℕ :=
  if i = 0 then [12, 48, 51, 204, 768, 3072] else [5, 48, 136, 320, 522, 3072]

@[expose] def commPairs (i : ℕ) : List (ℕ × ℕ) :=
  if i = 0 then [(0, 10), (0, 11), (0, 12), (0, 13), (1, 5), (2, 5), (2, 6)] else [(0, 10), (0, 11), (1, 6), (1, 7), (2, 6), (6, 11)]

@[expose] def perfPairs (i : ℕ) : List (ℕ × ℕ) :=
  if i = 0 then [(1, 2), (1, 3), (1, 5), (1, 6), (3, 5), (5, 6)] else [(1, 2), (1, 4), (1, 5), (2, 4)]

@[expose] def pGens (i : ℕ) : List (Array ℕ) :=
  (commPairs i).map fun p => commR (n2Gens i)[p.1]! (n2Gens i)[p.2]!

@[expose] def dGens (i : ℕ) : List (Array ℕ) :=
  (perfPairs i).map fun p => commR (pGens i)[p.1]! (pGens i)[p.2]!

@[expose] def thetaRows : Array ℕ := ((List.range 12).map fun j => theta0N (2 ^ j)).toArray

@[expose] def gensOK (gs : List (Array ℕ)) : Bool :=
  gs.all fun g => okRows g && okRows (invR g) && mulR g (invR g) == idR && mulR (invR g) g == idR

@[expose] def indepCheck : List ℕ → Bool
  | [] => true
  | v :: vs => !((spanList vs).contains v) && indepCheck vs

@[expose] def orbitPts (gs : List (Array ℕ)) : List ℕ :=
  bfsClosure (fun x : ℕ => x) (gs.map appN) 4096 [a0] ((∅ : Std.HashSet ℕ).insert a0) []

@[expose] def outPts (i : ℕ) : List ℕ :=
  (spanList (sigmaBasis i)).filter fun v => v != 0 && !((s45 i).contains v)

@[expose] def inF4Span (x y w : ℕ) : Bool :=
  (spanList [x, theta0N x, y, theta0N y]).contains w

@[expose] def orbitOK (W : List (Array ℕ × Array ℕ)) (S OP : List ℕ) : Bool :=
  S.contains a0 && S.all (fun x => W.all fun p => S.contains (appN p.1 x) && S.contains (appN p.2 x)) &&
    S.all OP.contains

@[expose] def sigmaOK (S B SP : List ℕ) : Bool :=
  B.all S.contains && S.all SP.contains && SP.all (fun v => !q0b v) &&
    B.all (fun b => SP.contains (theta0N b)) && indepCheck B && B.length == 6

@[expose] def ovalOK (O : List ℕ) : Bool :=
  O.length == 18 && O.all (fun x => O.all fun y => O.all fun w =>
    !(f4Indep x y && f4Indep x w && f4Indep y w) || !(inF4Span x y w))

@[expose] def pOK (W : List (Array ℕ × Array ℕ)) (PG XP : List (Array ℕ))
    (HP : Std.HashSet (Array ℕ)) : Bool :=
  XP.contains idR && closedCheck PG XP && XP.dedup.length == 17280 && HP.contains thetaRows &&
    W.all (fun a => W.all fun b => HP.contains (mulR a.1 (mulR b.1 (mulR a.2 b.2)))) &&
    XP.all (fun x => W.all fun p =>
      HP.contains (mulR p.1 (mulR x p.2)) && HP.contains (mulR p.2 (mulR x p.1)))

@[expose] def dOK (DG XD : List (Array ℕ)) : Bool :=
  XD.contains idR && closedCheck DG XD && XD.dedup.length == 17280

@[expose] def centOK (B : List ℕ) (PG XP : List (Array ℕ)) : Bool :=
  XP.any fun c => B.all (fun b => appN c b == b) && PG.any fun p => mulR c p != mulR p c

@[expose] def idxOK (i : ℕ) : Bool :=
  (commPairs i).all (fun p => p.1 < (n2Gens i).length && p.2 < (n2Gens i).length) &&
    (perfPairs i).all (fun p => p.1 < (pGens i).length && p.2 < (pGens i).length)

@[expose] def sigmaCheckAt (i : ℕ) : Bool :=
  let N := n2Gens i
  let S := s45 i
  let B := sigmaBasis i
  let PG := pGens i
  let DG := dGens i
  let XP := enumGrp PG
  let W := withInv N
  gensOK N && gensOK PG && gensOK DG && idxOK i &&
    orbitOK W S (orbitPts N) && sigmaOK S B (spanList B) && ovalOK (outPts i) &&
    pOK W PG XP (Std.HashSet.ofList XP) && dOK DG (enumGrp DG) && centOK B PG XP

@[expose] def sigmaCheck (_ : Unit := ()) : Bool := sigmaCheckAt 0 && sigmaCheckAt 1

end CFSG.GF2Type.Smith1979.GammaU.SigmaP
