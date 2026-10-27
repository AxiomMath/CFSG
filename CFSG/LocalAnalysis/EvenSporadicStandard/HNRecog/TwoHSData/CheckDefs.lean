module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.WordData

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native

@[expose] def gensOK : Bool :=
  h1408Gens.all fun g => permOK 1408 g && invOK 1408 g (invT 1408 g)

@[expose] def wordOK (w : List ℕ) : Bool := w.all fun l => decide (1 ≤ l ∧ l ≤ 7)

@[expose] def closedOKH (n : Nat) (gens : Array Table) (L : Array Table) : Bool :=
  let M : Std.HashMap UInt64 Nat := Id.run do
    let mut m : Std.HashMap UInt64 Nat := {}
    for i in [0:L.size] do
      m := m.insert (hkey n L[i]!) i
    return m
  L.all fun x => gens.all fun g =>
    let y := compT n x g
    match M[hkey n y]? with
    | some i => (L[i]?.map (tblEq n y)).getD false
    | none => false

@[expose] def enumOKH (n cap m : Nat) (gs : List Table) : Bool :=
  let A := gs.toArray
  let E := mulClosureH n A cap
  gs.all (fun g => permOK n g && invOK n g (invT n g)) && mulTreeOK n A E.1 E.2.1 E.2.2 &&
    closedOKH n (A ++ A.map (invT n)) E.1 && hkeysDistinct n E.1.toList && E.1.size == m

@[expose] def tabsW (ws : List (List ℕ)) : List Table := ws.map tabW

@[expose] def enumW (cap m : Nat) (ws : List (List ℕ)) : Bool :=
  gensOK && ws.all wordOK && enumOKH 1408 cap m (tabsW ws)

@[expose] def classList (cap : Nat) (w : List ℕ) : Array Table :=
  (conjClosureH 1408 h1408Gens.toArray (h1408Gens.toArray.map (invT 1408)) (tabW w) cap).1

@[expose] def subgroupList (cap : Nat) (ws : List (List ℕ)) : Array Table :=
  (mulClosureH 1408 (tabsW ws).toArray cap).1

structure WClass where
  rep : List ℕ
  classSize : ℕ
  centOrder : ℕ
  centGens : List (List ℕ)

@[expose] def wclassOK (cap : Nat) (r : WClass) : Bool :=
  let pg := h1408Gens.toArray
  let pgInv := pg.map (invT 1408)
  let t := tabW r.rep
  let o := conjClosureH 1408 pg pgInv t cap
  let cg := (tabsW r.centGens).toArray
  let C := mulClosureH 1408 cg cap
  gensOK && wordOK r.rep && r.centGens.all wordOK &&
    conjTreeOK 1408 pg pgInv t o.1 o.2.1 o.2.2 && hkeysDistinct 1408 o.1.toList &&
    o.1.size == r.classSize && cg.all (fun c => commTT 1408 c t) &&
    mulTreeOK 1408 cg C.1 C.2.1 C.2.2 && hkeysDistinct 1408 C.1.toList &&
    C.1.size == r.centOrder && r.classSize * r.centOrder == 177408000

end CFSG.EvenSporadicStandard.HNRecog
