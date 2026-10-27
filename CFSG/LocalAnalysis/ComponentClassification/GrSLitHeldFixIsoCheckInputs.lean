module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixGraph
public import CFSG.Sporadic.SmallOddCore.HeLocalCheck
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourCertificate
public meta import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixGraph
public meta import CFSG.Sporadic.SmallOddCore.HeLocalCheck
public meta import CFSG.Sporadic.SmallOddCore.ClassSimple
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic
public meta import Certificates.Data.CFSGNative.PSL3Four.Certificate

public section

namespace CFSG.ComponentClassification.GrSLit.HeldFix

open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore

@[expose] def heldFixXWords : List (List ℕ) := [[0], [4, 3, 4, 3], [1, 3, 4, 3, 4, 1]]

@[expose] def heldFixSWords : List (List ℕ) :=
  [[0], [2, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 0, 1, 0, 0], [2, 0, 1, 0, 1, 0, 0, 2, 0],
    [1, 0, 2, 0, 2, 1, 0, 2, 1, 0, 1, 0, 2, 0], [1, 0, 2, 0, 2, 0, 1, 0, 2, 1, 0, 0]]

@[expose] def heldFixGraphGens : Array Tab :=
  Array.ofFn (n := 8) fun k =>
    if k.val < 5 then
      catTab 105 42 heDGens[k.val]! (wordTabS 42 gensS (heldFixSWords.getD k.val []))
    else
      catTab 105 42 (wordTabS 105 heDGens (heldFixXWords.getD (k.val - 5) [])) gensS[k.val - 5]!

@[expose] def heldFixGraphEnum : Enum := enumBFS 147 heldFixGraphGens 20160

end CFSG.ComponentClassification.GrSLit.HeldFix
