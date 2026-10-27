module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchL2Data

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

@[expose] def t1Par (c : ℕ) : ℕ := if c < 65536 then sTree.1[c]! else c - 65536

@[expose] def t1Pj (c : ℕ) : ℕ := if c < 65536 then sTree.2.1[c]! else 9

@[expose] def t1Dep (c : ℕ) : ℕ := if c < 65536 then sTree.2.2[c]! else sTree.2.2[c - 65536]! + 1

@[expose] def t1Vec (vS : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 131072) fun c => if c.val < 65536 then vS[c.val]! else vS[c.val - 65536]! ^^^ 512

@[expose] def sVecOK (vS : Array ℕ) : Bool :=
  vS[0]! == 0 && (List.range 65536).all fun c => decide (vS[c]! < 512) &&
    (c == 0 || vS[c]! == (vS[sTree.1[c]!]! ^^^ 2 ^ sTree.2.1[c]!))

@[expose] def l2eCharOK (j : ℕ) (vec : Array ℕ) (RW : List (ℕ × ℕ)) (IV : List ℕ) : Bool :=
  let mul := t1Mul (s2F j) (s2Z j)
  (RW.all fun p => decide (p.1 < 131072) && decide (p.2 < 10)) &&
    IV == (kInv mul 131072).map (fun c => vec[c]!) &&
    (List.range 1024).all fun b => b == 512 || b == 768 ||
      (RW.any fun p => chiV 10 b (s2Rel mul vec p.1 p.2)) ||
      (IV.filter fun v => !chiV 10 b v).length != 3839 ||
      ((List.range 131072).filter fun c => !chiV 10 b vec[c]! &&
        (mul c c != 0 && mul (mul c c) (mul c c) == 0)).length != 41216

@[expose] def l2eIW (j e : ℕ) : ℕ :=
  wprodN (t1Mul (s2F j) (s2Z j)) 7 (fun l => (s2Iota.getD j []).getD l 0) e

@[expose] def l2eIL (j a : ℕ) : ℕ :=
  wprodN (t1Mul (s2F j) (s2Z j)) 9 (fun i => (s2Iota.getD j []).getD (7 + i) 0) a

@[expose] def l2eIotaOK (j : ℕ) (vec : Array ℕ) : Bool :=
  let mul := t1Mul (s2F j) (s2Z j)
  let inv := t1Inv (s2F j) (s2Z j)
  let ι := s2IotaTab mul (s2Iota.getD j [])
  let ρ := fun i => (s2Iota.getD j []).getD (7 + i) 0
  ((s2Iota.getD j []).all fun c => decide (c < 131072)) && (s2Iota.getD j []).length == 16 &&
    ((List.range 65536).all fun c => c == 0 || ι[c]! != 0) &&
    (sGens.all fun g => s2InSp vec ι[g]!) &&
    ([128, 34816].all fun g => decide (a9K.co g < 512) && a9K.lin (a9K.co g) == g) &&
    ((List.range 9).all fun i => mul (ρ i) (ρ i) == 0 &&
      (List.range 9).all fun i' => mul (ρ i) (ρ i') == mul (ρ i') (ρ i)) &&
    ((List.range 7).all fun l => (List.range 9).all fun i =>
      cconj mul inv ι[sPc.getD l 0]! (ρ i) == l2eIL j (sAutData.cb l i)) &&
    (List.range 128).all fun e => (List.range 7).all fun l =>
      ι[sMul (wprodN sMul 7 (fun l' => sPc.getD l' 0) e) (sPc.getD l 0)]! ==
        mul (l2eIW j e) ι[sPc.getD l 0]!

@[expose] def l2eRecsOK (j : ℕ) (Rs : List (ℕ × List (ℕ × ℕ))) : Bool :=
  Rs.all fun q => decide (q.1 < 131072) &&
    orbOKM (t1Mul (s2F j) (s2Z j)) (t1Inv (s2F j) (s2Z j)) 131072 q.1 q.2 &&
    orbClosedM (t1Mul (s2F j) (s2Z j)) (t1Inv (s2F j) (s2Z j)) t1Gens q.1 q.2

@[expose] def l2eRec (Rs : List (ℕ × List (ℕ × ℕ))) (r : ℕ) : List ℕ :=
  ((Rs.find? fun q => q.1 == r).map fun q => q.2.map Prod.fst).getD []

@[expose] def l2eCentOK (j : ℕ) (vec : Array ℕ) (C3 : List ℕ) (O3 : List (ℕ × ℕ)) : Bool :=
  let mul := t1Mul (s2F j) (s2Z j)
  let inv := t1Inv (s2F j) (s2Z j)
  let ι := s2IotaTab mul (s2Iota.getD j [])
  s2InSp vec 3 && orbOKM mul inv 131072 3 O3 && orbClosedM mul inv t1Gens 3 O3 &&
    ((C3.zip C3.tail).all fun p => decide (p.1 < p.2)) &&
    (C3.all fun c => decide (c < 131072) && mul c 3 == mul 3 c) &&
    C3.length * O3.length == 131072 &&
    C3.all fun c => c == 0 || c == 24 || !(sGens.all fun g => mul c ι[g]! == mul ι[g]! c)

@[expose] def l2eActR (j k m w v : ℕ) (Rs : List (ℕ × List (ℕ × ℕ))) : Bool :=
  let B := s2B (t1Mul (s2F j) (s2Z j)) (s2IotaTab (t1Mul (s2F j) (s2Z j)) (s2Iota.getD j []))
    (sFm k m) w
  ((kRepsC (t1Cls (s2K j) (s2M j) (s2Z j)) 16).all fun r => l2Fix.contains r ||
    ((Rs.any fun q => q.1 == r) && !(l2eRec Rs r).contains (B r))) &&
    (t1Gens.all fun g => (chiS 131072)[B g]! == (chiS 131072)[g]!) && !(chiS 131072)[v]!

@[expose] def l2eActOK (j k m w : ℕ) (Rs : List (ℕ × List (ℕ × ℕ))) (a : ℕ × ℕ × ℕ) : Bool :=
  let mul := t1Mul (s2F j) (s2Z j)
  let inv := t1Inv (s2F j) (s2Z j)
  let B := s2B mul (s2IotaTab mul (s2Iota.getD j [])) (sFm k m) w
  decide (a.2.1 < 131072) &&
    if a.1 == 0 then (l2eRec Rs a.2.2).contains a.2.1 && !(l2eRec Rs a.2.2).contains (B (B a.2.1))
    else ((List.range 10).all fun i =>
        cconj mul inv a.2.1 (t1Gens.getD i 0) == B (B (t1Gens.getD i 0))) &&
      ((s2Canon.getD j []).contains (k, m, w, a.2.1) ||
        (l2eActR j k m w a.2.1 Rs && l2eActR j k m w (mul a.2.1 24) Rs))

@[expose] def l2eLeafOK (j : ℕ) (Rs : List (ℕ × List (ℕ × ℕ))) (k m : ℕ)
    (lw : ℕ × ℕ × ℕ × List (ℕ × ℕ × ℕ)) : Bool :=
  let mul := t1Mul (s2F j) (s2Z j)
  let ι := s2IotaTab mul (s2Iota.getD j [])
  let F := sFm k m
  if lw.1 == 0 then decide (lw.2.1 < 65536) && (l2eRec Rs lw.2.2.1).contains ι[F lw.2.1]! &&
    !(l2eRec Rs lw.2.2.1).contains ι[F (s2F j)[lw.2.1]!]!
  else decide (lw.2.1 < 131072) &&
    ((List.range 9).all fun i => mul lw.2.1 ι[F (sGens.getD i 0)]! ==
      mul ι[F (s2F j)[sGens.getD i 0]!]! lw.2.1) &&
    match lw.2.2.2 with
    | [a₀, a₁] => l2eActOK j k m lw.2.1 Rs a₀ && l2eActOK j k m (mul lw.2.1 24) Rs a₁
    | _ => false

@[expose] def l2eEnumOK (j : ℕ) (vec : Array ℕ) (Rs : List (ℕ × List (ℕ × ℕ))) (C3 : List ℕ)
    (O3 : List (ℕ × ℕ)) (LW : List (ℕ × ℕ × ℕ × List (ℕ × ℕ × ℕ))) : Bool :=
  l2eRecsOK j Rs && l2eCentOK j vec C3 O3 &&
    (List.range 8).all fun k => (List.range (sLeaves k).length).all fun m =>
      l2eLeafOK j Rs k m (LW.getD (32 * k + m) (0, 0, 0, []))

structure L2EW where
  vS : Array ℕ
  RW : List (ℕ × ℕ)
  IV : List ℕ
  Rs : List (ℕ × List (ℕ × ℕ))
  C3 : List ℕ
  O3 : List (ℕ × ℕ)
  LW : List (ℕ × ℕ × ℕ × List (ℕ × ℕ × ℕ))

@[expose] def l2eSurvOK (j : ℕ) (W : L2EW) : Bool :=
  sVecOK W.vS && l2eCharOK j (t1Vec W.vS) W.RW W.IV && l2eIotaOK j (t1Vec W.vS) &&
    l2eEnumOK j (t1Vec W.vS) W.Rs W.C3 W.O3 W.LW

end CFSG.EvenSmallLie.OmegaEight.SpBranch

end
