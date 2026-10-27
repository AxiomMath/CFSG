module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.CheckDefs

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

@[expose] def cayleyImages {T : Type} [Group T] (ts : Array T) (par lab : Array ℕ) : Array T :=
  Id.run do
    let mut fv : Array T := #[1]
    for k in [1:par.size] do
      fv := fv.push (fv.getD (par.getD k 0) 1 * ts.getD (lab.getD k 0) 1)
    return fv

@[expose, noinline] def cayleyStepOK {T : Type} [Group T] [DecidableEq T] (L gs : Array Table)
    (ts fv : Array T) : Bool :=
  allIn 0 L.size fun k => allIn 0 gs.size fun i =>
    let y := compT 1408 L[k]! gs[i]!
    let v := fv.getD k 1 * ts.getD i 1
    (List.range L.size).any fun j => tblEq 1408 y L[j]! && decide (fv.getD j 1 = v)

@[expose] def distinctOK {T : Type} [DecidableEq T] (fv : Array T) (one : T) : Bool :=
  allIn 0 fv.size fun a => allIn (a + 1) fv.size fun b =>
    decide (fv.getD a one ≠ fv.getD b one)

@[expose] def cayleyOK {T : Type} [Group T] [DecidableEq T] (cap m : ℕ) (ws : List (List ℕ))
    (ts : List T) : Bool :=
  let E := mulClosureH 1408 (tabsW ws).toArray cap
  let fv := cayleyImages ts.toArray E.2.1 E.2.2
  enumW cap m ws && (ws.length == ts.length) && decide (0 < E.1.size) &&
    tblEq 1408 E.1[0]! (idT 1408) && (fv.size == E.1.size) && decide (fv.getD 0 1 = 1) &&
    cayleyStepOK E.1 (tabsW ws).toArray ts.toArray fv && distinctOK fv 1

end CFSG.EvenSporadicStandard.HNRecog
