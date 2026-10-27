module

public import CFSG.Sporadic.SmallOddCore.McLLocalCheck
public meta import CFSG.Sporadic.SmallOddCore.McLLocalCheck
public meta import CFSG.Sporadic.SmallOddCore.McLData
public meta import CFSG.Sporadic.SmallOddCore.ClassSimple
public meta import CFSG.Sporadic.SuzOddCore.RestrictDefs
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic

public section

namespace CFSG.ComponentClassification.RestrictedStd.Spor

open CFSG.PSL3Four.Native CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native

@[expose] def mclU1Arr : Array Nat := natArr (mclCentTbl 17)

@[expose] def mclFix1 : List Nat := fixedList 275 mclU1Arr

@[expose] def mclYGens : Array Tab :=
  Array.ofFn (n := 4) fun k => restrictArr mclFix1 (natArr (mclCentTbl (k.val + 18)))

@[expose] def mclYInvs : Array Tab := mclYGens.map (invTab 11)

@[expose] def mclYWords : List (List Nat) :=
  [[], [1], [0], [0, 3, 3], [1, 0], [0, 3], [3, 2, 2], [2, 3, 3], [2], [2, 2]]

@[expose] def mclYSizes : List Nat := [1, 165, 440, 990, 1584, 1320, 990, 990, 720, 720]

@[expose] def mclYEnum : Enum := enumBFS 11 mclYGens 7920

@[expose] def mclYOrbits : Array Enum :=
  Array.ofFn (n := 10) fun l => orbitBFS 11 mclYGens mclYInvs (wordTabS 11 mclYGens
    (mclYWords.getD l.val [])) 2000

end CFSG.ComponentClassification.RestrictedStd.Spor
