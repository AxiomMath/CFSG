module

public import CFSG.Sporadic.SuzOddCore.InvTCheckInputs
public import CFSG.Sporadic.SuzOddCore.InvArrays
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzN0Tbl
public import Certificates.Data.CFSGNative.PSL3Four.Basic
public import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.Sporadic.SuzOddCore.InvTCheckInputs
public meta import CFSG.Sporadic.SuzOddCore.InvArrays
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzN0Tbl
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic
public meta import Certificates.Data.CFSGNative.Schreier.Check

public section

namespace CFSG.EvenSporadicStandard.SuzN0

open CFSG.PSL3Four.Native CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native

@[expose] def gens0 : Array Tab := invInnerGenArrs 0

@[expose] def xTab (j : Nat) : Tab :=
  commTab 1782 gens0[1]! gens0[j + 2]! (invTab 1782 gens0[1]!) (invTab 1782 gens0[j + 2]!)

@[expose] def xs : Array Tab := Array.ofFn (n := 5) fun j => xTab j.val

@[expose] def xsInv : Array Tab := xs.map (invTab 1782)

@[expose] def letterX (l : Int) : Tab :=
  if 0 < l then xs[l.toNat - 1]! else xsInv[(-l).toNat - 1]!

@[expose] def wordX (w : List Int) : Tab :=
  w.foldr (fun l acc => comp 1782 (letterX l) acc) (idTab 1782)

@[expose] def powTab (t : Tab) : Nat → Tab
  | 0 => idTab 1782
  | m + 1 => comp 1782 t (powTab t m)

@[expose] def oddWords : List (List Int × Nat) :=
  [([-1], 3), ([1, 5, 5], 5), ([-1], 3), ([1, 4, 5, -4], 7), ([4, -1], 5), ([1, 4, -5], 7),
   ([-4], 5), ([-1, -2], 3), ([5, 2, 1], 3)]

@[expose] def oddTab (k : Nat) : Tab := wordX (oddWords.getD k ([], 1)).1

@[expose] def rTab (i : Nat) : Tab := comp 1782 (oddTab (2 * i)) (oddTab (2 * i + 1))

@[expose] def rTabs : Array Tab := Array.ofFn (n := 4) fun i => rTab i.val

@[expose] def wTab : Tab := oddTab 8

@[expose] def zWord : List Int := [-5, 4, 5, 4]

@[expose] def zTab : Tab := wordX zWord

@[inline, expose] def app3 (a b c : Tab) (x : Nat) : Nat := a[b[c[x]!]!]!

@[expose] def commPts (a b c s : Tab) : Nat → Bool
  | 0 => true
  | k + 1 => app3 a b c (s[k]!) == s[app3 a b c k]! && commPts a b c s k

@[expose] def commGens (a b c : Tab) (gs : Array Tab) : Nat → Bool
  | 0 => true
  | k + 1 => commPts a b c gs[k]! 1782 && commGens a b c gs k

@[expose] def commAll3 (a b c : Tab) (gs : Array Tab) : Bool := commGens a b c gs gs.size

@[expose] def survList (lev : Array Level) (gs : Array Tab) : List Tab :=
  (List.range lev[0]!.pts.size).flatMap fun k0 =>
    let a := lev[0]!.tr[k0]!
    (List.range lev[1]!.pts.size).flatMap fun k1 =>
      let b := lev[1]!.tr[k1]!
      (List.range lev[2]!.pts.size).filterMap fun k2 =>
        let c := lev[2]!.tr[k2]!
        if commAll3 a b c gs then some (comp 1782 (comp 1782 a b) c) else none

@[expose] def levD1 (_ : Unit := ()) : Array Level :=
  rawLevels 1782 (invFullStrongArrs 1) (invFullBases.getD 1 []).toArray

@[expose] def gensN (hI : Tab) : Array Tab :=
  (rTabs.push wTab).map (conjTab 1782 hI hTab)

@[expose] def survOK (surv : Array Tab) : Bool :=
  let sI := surv.map (invTab 1782)
  invsOK 1782 surv sI &&
    allBelow surv.size (fun i => inM surv[i]! &&
      (comp 1782 surv[i]! surv[i]! == idTab 1782 ||
        comp 1782 surv[i]! (comp 1782 surv[i]! surv[i]!) == idTab 1782)) &&
    allBelow surv.size (fun i => allBelow surv.size fun j =>
      let c := commTab 1782 surv[i]! surv[j]! sI[i]! sI[j]!
      comp 1782 c c == idTab 1782 &&
        (!(comp 1782 surv[i]! surv[i]! == idTab 1782 &&
            comp 1782 surv[j]! surv[j]! == idTab 1782) ||
          comp 1782 surv[i]! surv[j]! == comp 1782 surv[j]! surv[i]!)) &&
    decide ((surv.filter fun s => comp 1782 s s == idTab 1782).size ≤ 4)

@[expose] def suzN0CheckWith (hI wI : Tab) (ER : Enum) (surv : Array Tab) : Bool :=
  gens0.size == 22 && allBelow 22 (fun j => gens0[j]!.size == 1782) &&
    invsOK 1782 gens0 (gens0.map (invTab 1782)) &&
    invsOK 1782 xs xsInv &&
    oddWords.all (fun p => p.2 % 2 == 1 && powTab (wordX p.1) p.2 == idTab 1782) &&
    enumOK 1782 rTabs ER && ER.tabs.size == 64 &&
    found (indexOf ER.tabs) ER.tabs zTab &&
    invsOK 1782 #[wTab] #[wI] &&
    allBelow 4 (fun i => found (indexOf ER.tabs) ER.tabs (conjTab 1782 wTab wI (rTab i))) &&
    isInvA 1782 hTab hI && hTab.size == 1782 && hI.size == 1782 && inM hTab &&
    (tArr 1).size == 1782 &&
    conjTab 1782 hTab hI (tArr 1) == zTab && survOK surv

@[expose] def suzN0Check (_ : Unit := ()) : Bool :=
  let hI := invTab 1782 hTab
  let surv := (survList (levD1 ()) (gensN hI)).toArray
  suzN0CheckWith hI (invTab 1782 wTab) (enumBFS 1782 rTabs 64) surv

end CFSG.EvenSporadicStandard.SuzN0
