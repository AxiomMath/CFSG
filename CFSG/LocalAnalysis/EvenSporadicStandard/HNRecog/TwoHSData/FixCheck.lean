module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.CheckDefs

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

@[expose] def fixCount (T : Table) : ℕ := ((Finset.range 1408).filter fun p => ap T p = p).card

structure FixData where
  rep : List ℕ
  cent : List (List ℕ)
  centOrder : ℕ
  fix : ℕ
  conjs : List (List ℕ)
  m : ℕ

@[expose] def p0Tabs (ws : List (List ℕ)) : Array Table := (tabsW ws).toArray

@[expose] def p0Invs (ws : List (List ℕ)) : Array Table := (p0Tabs ws).map (invT 1408)

@[expose] def conjTab (c : List ℕ) (x : Table) : Table :=
  conjT 1408 (tabW c) (invT 1408 (tabW c)) x

@[expose] def fixClosures (cap : ℕ) (pg pgInv : Array Table) (tx : Table) (cs : List (List ℕ)) :
    List (Array Table × Array ℕ × Array ℕ) :=
  cs.map fun c => conjClosureH 1408 pg pgInv (conjTab c tx) cap

@[expose] def fixTreesOK (pg pgInv : Array Table) (tx : Table) :
    List (List ℕ) → List (Array Table × Array ℕ × Array ℕ) → Bool
  | c :: cs, o :: os =>
    conjTreeOK 1408 pg pgInv (conjTab c tx) o.1 o.2.1 o.2.2 && o.1.all (fun T => ap T 0 == 0) &&
      fixTreesOK pg pgInv tx cs os
  | [], [] => true
  | _, _ => false

@[expose] def fixClassOK (cap : ℕ) (p0w : List (List ℕ)) (d : FixData) : Bool :=
  let pg := p0Tabs p0w
  let pgInv := p0Invs p0w
  let tx := tabW d.rep
  let cls := fixClosures cap pg pgInv tx d.conjs
  gensOK && wordOK d.rep && d.cent.all wordOK && d.conjs.all wordOK && p0w.all wordOK &&
    p0w.all (fun w => invOK 1408 (tabW w) (invT 1408 (tabW w))) &&
    d.conjs.all (fun c => invOK 1408 (tabW c) (invT 1408 (tabW c))) &&
    enumW cap d.centOrder d.cent && d.cent.all (fun c => commTT 1408 (tabW c) tx) &&
    (ap tx 0 == 0) && (fixCount tx == d.fix) && fixTreesOK pg pgInv tx d.conjs cls &&
    hkeysDistinct 1408 (cls.flatMap fun o => o.1.toList) &&
    ((cls.map fun o => o.1.size).sum == d.m) &&
    (d.centOrder * 1408 * d.m == 177408000 * d.fix)

@[expose] def fixListsOf (cap : ℕ) (p0w : List (List ℕ)) (ds : List FixData) : List (Array Table) :=
  let pg := p0Tabs p0w
  let pgInv := p0Invs p0w
  ds.flatMap fun d => (fixClosures cap pg pgInv (tabW d.rep) d.conjs).map (·.1)

@[expose, noinline] def coverOK (idt : Table) (Ls : List (Array Table)) (S : Array Table) : Bool :=
  S.all fun y => tblEq 1408 y idt || Ls.any fun L => memT 1408 L y

@[expose] def fixPrimeOK (cap : ℕ) (p0w : List (List ℕ)) (ds : List FixData)
    (sw : List (List ℕ)) (sord : ℕ) : Bool :=
  ds.all (fixClassOK cap p0w) && enumW cap sord sw &&
    coverOK (idT 1408) (fixListsOf cap p0w ds) (subgroupList cap sw)

@[expose] def orbitTree (gens : Array Table) (cap : ℕ) : Array ℕ × Array ℕ × Array ℕ := Id.run do
  let mut seen : Array Bool := (Array.replicate 1408 false).set! 0 true
  let mut pts : Array ℕ := #[0]
  let mut par : Array ℕ := #[0]
  let mut lab : Array ℕ := #[0]
  for h in [0:cap] do
    if h < pts.size then
      let p := pts[h]!
      for l in [0:gens.size] do
        let q := ap gens[l]! p
        if q < 1408 && !seen[q]! then
          seen := seen.set! q true
          pts := pts.push q
          par := par.push h
          lab := lab.push l
    else break
  return (pts, par, lab)

@[expose] def orbitOK (gens : Array Table) (pts par lab : Array ℕ) : Bool :=
  0 < pts.size && pts[0]! == 0 &&
    allIn 1 pts.size (fun k =>
      par[k]! < k && lab[k]! < gens.size && pts[k]! == ap gens[lab[k]!]! pts[par[k]!]!) &&
    (List.range 1408).all fun p => pts.contains p

@[expose] def transOK : Bool :=
  let gens := h1408Gens.toArray
  let o := orbitTree gens 2000
  gensOK && orbitOK gens o.1 o.2.1 o.2.2

end CFSG.EvenSporadicStandard.HNRecog
