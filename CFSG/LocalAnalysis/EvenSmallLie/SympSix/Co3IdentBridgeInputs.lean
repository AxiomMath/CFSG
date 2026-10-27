module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentCard
public import CFSG.Sporadic.Bridge.VecSurj
public import CFSG.Sporadic.Co3
public meta import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentDefs
public meta import Certificates.Data.CFSGNative.Bridge.SurjD
import CFSG.Blueprint.NativeSporadic
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.EvenSmallLie.SympSix.Co3Ident

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.SurjD.Native
  CFSG.Sporadic.Bridge.VecSurj

@[expose] def sDok : List ℕ :=
  [1, 2, 5, 1, 6, 2, 1, 0, 6, 2, 1, 0, 5, 6, 2, 5, 1, 3, 2, 4, 3, 5, 6, 0, 2, 6]

@[expose] def vImgWords : Array (List Int) :=
  let W := parseWords co3ImgText
  W.set! 3 (sDok.flatMap fun i => W[i]!)

@[expose] def substD (z : Int) : List Int :=
  if z = 4 then [4, 6, 7, 4] else if z = -4 then [-4, -7, -6, -4] else [z]

@[expose] def vSurjWords : Array (List Int) :=
  (parseWords co3SurjText).map fun w => w.flatMap substD

@[expose] def vRels : List (List (ℕ × Bool)) := relsV.map (List.map fun l => (l.1.val, l.2))

@[expose] def vSpec : Spec := ⟨7, vRels, vImgWords, vSurjWords⟩

end CFSG.EvenSmallLie.SympSix.Co3Ident
