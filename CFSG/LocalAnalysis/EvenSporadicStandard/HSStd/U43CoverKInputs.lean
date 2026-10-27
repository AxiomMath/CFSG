module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Inputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43CoverData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43CoverKBData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43CoverKCData
public import CFSG.Sporadic.SmallOddCore.CentData
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Inputs
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43CoverData
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43CoverKBData
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43CoverKCData
public meta import CFSG.Sporadic.SmallOddCore.CentData
public meta import Certificates.Data.CFSGNative.SmallOddCore.Check

public section

namespace CFSG.EvenSporadicStandard.HSStd.U43

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.EvenSporadicStandard.M24Std.CU43

@[expose] def commTab (a b : Table) : Table :=
  compT 820 (compT 820 a b) (compT 820 (invT 820 a) (invT 820 b))

@[expose] def cubeTab (p : Table) : Table := compT 820 p (compT 820 p p)

@[expose] def kTabs (y : Table) (cs : List (Table × Table)) (ps : List Table) : Array Table :=
  (y :: (cs.map fun c => commTab c.1 c.2) ++ ps.map cubeTab).toArray

@[expose] def kCap : ℕ := 400

@[expose] def memCheck (y a : Table) : Bool :=
  permOK 820 a && CFSG.Sporadic.Th.Native.invOK 820 a (invT 820 a) && inP (natArr a) &&
    commTT 820 a y

@[expose] def kRepCheck (y : Table) (cs : List (Table × Table)) (ps : List Table) : Bool :=
  permOK 820 y && (cs.all fun c => memCheck y c.1 && memCheck y c.2) && ps.all (memCheck y) &&
    (kTabs y cs ps).all (fun x => permOK 820 x &&
      CFSG.Sporadic.Th.Native.invOK 820 x (invT 820 x)) &&
    mulTreeOK 820 (kTabs y cs ps) (mulClosureH 820 (kTabs y cs ps) kCap).1
      (mulClosureH 820 (kTabs y cs ps) kCap).2.1 (mulClosureH 820 (kTabs y cs ps) kCap).2.2 &&
    closedOK 820 (kTabs y cs ps ++ (kTabs y cs ps).map (invT 820))
      (mulClosureH 820 (kTabs y cs ps) kCap).1 &&
    hkeysDistinct 820 (mulClosureH 820 (kTabs y cs ps) kCap).1.toList &&
    (mulClosureH 820 (kTabs y cs ps) kCap).1.size == 324

@[expose] def kBComm : List (Table × Table) :=
  [(kB1a.map UInt32.ofNat, kB1b.map UInt32.ofNat), (kB3a.map UInt32.ofNat, kB3b.map UInt32.ofNat)]

@[expose] def kBCube : List Table := [kB2p.map UInt32.ofNat]

@[expose] def kCComm : List (Table × Table) :=
  [(kC1a.map UInt32.ofNat, kC1b.map UInt32.ofNat), (kC3a.map UInt32.ofNat, kC3b.map UInt32.ofNat),
    (kC4a.map UInt32.ofNat, kC4b.map UInt32.ofNat)]

@[expose] def kCCube : List Table := [kC2p.map UInt32.ofNat]

@[expose] def kCheck : Bool :=
  kRepCheck yBTab kBComm kBCube && kRepCheck yCTab kCComm kCCube

end CFSG.EvenSporadicStandard.HSStd.U43
