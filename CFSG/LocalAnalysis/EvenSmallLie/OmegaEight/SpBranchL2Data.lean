module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchL2K
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchL2P
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchL2Cent

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

@[expose] def l2Like : List ℕ := [64, 67, 75, 2371]

@[expose] def l2O4 : List ℕ := [10336, 10336, 9312, 9312]

@[expose] def l2Fix : List ℕ := [3, 1539]

@[expose] def l2T : List ℕ := [64, 75]

@[expose] def l2PLit : List (List (ℕ × ℕ)) :=
  [[(1055, 5600), (1183, 5472), (671, 4960), (799, 4832), (991, 6688), (863, 4768), (735, 3872),
      (735, 4896), (607, 6048)],
    [(1055, 5600), (1183, 5472), (1055, 4576), (671, 3936), (799, 3808), (671, 4960), (991, 5664),
      (863, 4768), (735, 3872), (863, 3744), (607, 5024), (735, 4896)]]

@[expose] def vecOf (L : List (ℕ × ℕ × ℕ × ℕ)) (c : ℕ) : ℕ :=
  ((L.find? fun e => e.1 == c).map fun e => e.2.2.2).getD 0

@[expose] def l2THOK (e : ℕ) (gs : List ℕ) (ps : List (ℕ × ℕ)) : Bool :=
  let t := l2T.getD e 0
  let L := dblL sMul gs ps
  decide (gs.length ≤ 5) &&
    (gs.all fun g => decide (g < 65536) && sMul g t == sMul t g) &&
    (ps.all fun st => decide (st.2 < gs.length) ||
      (decide (st.1 < 65536) && sMul st.1 t == sMul t st.1)) &&
    nodupM (L.map Prod.fst) && L.length == 16384 &&
    ((List.range 65536).filter fun c => sMul c t == sMul t c).length == 16384 &&
    ((List.range 32).all fun b => b == 0 || chiV 5 b (vecOf L t) ||
      (l2PLit.getD e []).contains
        (cntMask 5 b (fun c => sMul c c == 0 && c != 0) L,
          cntMask 5 b (fun c => sMul c c != 0 && sMul (sMul c c) (sMul c c) == 0) L))

@[expose] def l2SurvOK (j : ℕ) (I : List ℕ) (cents : List (ℕ × List ℕ × ℕ × ℕ))
    (recs : List (ℕ × List ℕ)) : Bool :=
  let mul := t1Mul (s2F j) (s2Z j)
  let inv := t1Inv (s2F j) (s2Z j)
  let C := t1Cls (s2K j) (s2M j) (s2Z j)
  (cents.all (centOK3 mul inv t1Gens 131072 32)) && I == kInv mul 131072 &&
    ((kRepsC C 8).all fun r => l2Like.contains r || kCount mul I r != 1439) &&
    (l2Fix.all fun r => (cents.map Prod.fst).contains r) &&
    (cents.all fun e => !l2Fix.contains e.1 || !l2PLit.flatten.contains (e.2.2.1, e.2.2.2)) &&
    ((l2Like.zip l2O4).all fun p => cents.any fun e => e.1 == p.1 && e.2.2.1 == 1439 &&
      e.2.2.2 == p.2) &&
    ((kRepsC C 16).all fun r => recs.any fun q => q.1 == r &&
      q.2 == (recM mul inv t1Gens r).map Prod.fst)

@[expose] def l2KOK (j : ℕ) (gs : List ℕ) (L : List (ℕ × ℕ × ℕ × ℕ)) : Bool :=
  kDataOK sMul 65536 (kInv sMul 65536)
      (s2IotaTab (t1Mul (s2F j) (s2Z j)) (s2Iota.getD j [])) gs L && L.length == 64

@[expose] def l2ActOK (j k m w v : ℕ) (recs : List (ℕ × List ℕ)) : Bool :=
  let mul := t1Mul (s2F j) (s2Z j)
  let ι := s2IotaTab mul (s2Iota.getD j [])
  (recs.all fun q => l2Fix.contains q.1 || !q.2.contains (s2B mul ι (sFm k m) w q.1)) &&
    (t1Gens.all fun g => (chiS 131072)[s2B mul ι (sFm k m) w g]! == (chiS 131072)[g]!) &&
    !(chiS 131072)[v]!

@[expose] def l2SurvActOK (j : ℕ) (I : List ℕ) (cents : List (ℕ × List ℕ × ℕ × ℕ))
    (recs : List (ℕ × List ℕ)) : Bool :=
  l2SurvOK j I cents recs &&
    ((s2Canon.getD j []).all fun e => l2ActOK j e.1 e.2.1 e.2.2.1 e.2.2.2 recs &&
      l2ActOK j e.1 e.2.1 e.2.2.1 (t1Mul (s2F j) (s2Z j) e.2.2.2 24) recs)

end CFSG.EvenSmallLie.OmegaEight.SpBranch

end
