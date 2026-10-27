module

public import CFSG.Sporadic.SuzOddCore.SylowCheckInputs
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step18SuzCenterData
public meta import CFSG.Sporadic.SuzOddCore.SylowCheckInputs

public section

namespace CFSG.ComponentClassification.AS81.SuzCenter

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.PSL3Four.Native
open CFSG.Sporadic.SuzOddCore

@[expose] def commAll (gs : Array Tab) (t : Tab) : Bool :=
  allBelow gs.size fun k => comp 1782 t gs[k]! == comp 1782 gs[k]! t

@[expose] def wordC (gs : Array Tab) (w : List Nat) : Tab :=
  w.foldr (fun j acc => comp 1782 gs[j]! acc) (idTab 1782)

@[expose] def sylLetters : Array Tab := invSylowArrs.push (invCand 1782 invSylowArrs[0]!)

@[expose] def sylMGens : Array Tab := (sylMWords.map (wordC sylLetters)).toArray

@[expose] def levelGens (gs : Array Tab) (L : CentreLevel) : Array Tab :=
  (L.ws.map (wordC gs)).toArray

@[expose] def fixesAll (t : Tab) (ps : List Nat) : Bool := ps.all fun p => t[p]! == p

@[expose] def treeOK (hs : Array Tab) (L : CentreLevel) : Bool :=
  L.par.length == L.pts.length && L.gen.length == L.pts.length && L.pts.head? == some L.b &&
    decide L.pts.Nodup && L.pts.all (· < 1782) &&
    (List.range L.pts.length).all fun j => j == 0 ||
      (decide (L.par[j]! < j) && decide (L.gen[j]! < hs.size) &&
        hs[L.gen[j]!]![L.pts[L.par[j]!]!]! == L.pts[j]!)

@[expose] def levelsOK (gs : Array Tab) : List Nat → List CentreLevel → Bool
  | _, [] => true
  | B, L :: Ls => L.ws.all (·.all (· < gs.size)) && (levelGens gs L).all (fixesAll · B) &&
      treeOK (levelGens gs L) L && levelsOK gs (B ++ [L.b]) Ls

@[expose] def centreOK (gs : Array Tab) (zw : List Nat) (Ls : List CentreLevel) (N : Nat) : Bool :=
  match Ls with
  | L0 :: L1 :: _ =>
    levelsOK gs [] Ls && (Ls.map (·.pts.length)).prod == N &&
      (L0.pts.all fun x => allBelow gs.size fun k => L0.pts.contains gs[k]![x]!) &&
      Ls.all (fun L => L0.pts.contains L.b) &&
      (L0.pts.filter fun x => (levelGens gs L1).all fun h => h[x]! == x).length == 2 &&
      zw.all (· < gs.size) && commAll gs (wordC gs zw) && !(fixesAll (wordC gs zw) L0.pts)
  | _ => false

@[expose] def suzSylowCenterCheck : Bool :=
  centreOK invSylowArrs sylSZWord sylSLevels 16384 &&
    (allBelow sylMGens.size fun k => permOK 1782 sylMGens[k]! && inM sylMGens[k]!) &&
    centreOK sylMGens sylRZWord sylRLevels 8192

end CFSG.ComponentClassification.AS81.SuzCenter
