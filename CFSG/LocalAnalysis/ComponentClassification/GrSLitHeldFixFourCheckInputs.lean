module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixSylowCheck
public import CFSG.Sporadic.HeldB.CertPFieldsData
public meta import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixSylowCheck
public meta import CFSG.Sporadic.HeldB.CertPFieldsData
public meta import CFSG.Sporadic.HeldB.InnerCheck
public meta import CFSG.Sporadic.HeldB.OuterArithCheck
public meta import CFSG.Sporadic.SmallOddCore.ClassSimple
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic

public section

namespace CFSG.ComponentClassification.GrSLit.HeldFix

open CFSG.PSL3Four.Native CFSG.Sporadic.HeldB CFSG.Sporadic.SmallOddCore
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def hfKTab : Tab := wordA 8330 heABArrs (heABArrs.map (invCand 8330)) hfKWord

@[expose] def hfB1Tabs : Array Tab :=
  Array.ofFn (n := 2) fun i => wordTabS 8330 hfTTabs (hfB1Words.getD i.val [])

@[expose] def hfB1Elems : List Tab :=
  [idTab 8330, hfB1Tabs[0]!, hfB1Tabs[1]!, comp 8330 hfB1Tabs[0]! hfB1Tabs[1]!]

@[expose] def hfE2Tab : Tab := wordTabS 8330 hfTTabs hfE2Word

@[expose] def hfConjK (s : Tab) : Tab := comp 8330 (comp 8330 hfKTab s) (invCand 8330 hfKTab)

@[expose] def hfOrbGens : Array Tab :=
  (heStabIdx.map fun j => hfConjK (heStrong j)).toArray ++ hfTTabs

@[expose] def hfPointBFS (n : Nat) (gens : Array Tab) (root : Nat) :
    Array Nat × Array Nat × Array Nat := Id.run do
  let mut pts : Array Nat := #[root]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  let mut seen : Array Bool := (Array.replicate n false).set! root true
  for h in [0:n] do
    if h < pts.size then
      let p := pts[h]!
      for j in [0:gens.size] do
        let q := (gens[j]!)[p]!
        if !(seen[q]!) then
          seen := seen.set! q true
          pts := pts.push q
          par := par.push h
          lab := lab.push j
  return (pts, par, lab)

@[expose] def hfPositions (n : Nat) (pts : Array Nat) : Array Nat := Id.run do
  let mut pos : Array Nat := Array.replicate n 0
  for i in [0:pts.size] do
    pos := pos.set! pts[i]! i
  return pos

@[expose] def hfPointTreeOK (n : Nat) (gens : Array Tab) (root : Nat)
    (pts par lab pos : Array Nat) : Bool :=
  pts.size == n && pts[0]! == root &&
    allBelow n (fun i => i == 0 || (decide (par[i]! < i) && decide (lab[i]! < gens.size) &&
      (gens[lab[i]!]!)[pts[par[i]!]!]! == pts[i]!)) &&
    allBelow n fun x => decide (pos[x]! < n) && pts[pos[x]!]! == x

@[expose] def hfOrbTree : Array Nat × Array Nat × Array Nat := hfPointBFS 8330 hfOrbGens 7750

end CFSG.ComponentClassification.GrSLit.HeldFix
