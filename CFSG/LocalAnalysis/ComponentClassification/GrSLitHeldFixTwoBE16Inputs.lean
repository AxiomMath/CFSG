module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixTwoBCheckInputs
public import CFSG.Assembly.LowTwoRankDefs

public noncomputable section

namespace CFSG.ComponentClassification.GrSLit.HeldFix

open CFSG.ComponentClassification.PSL3Four CFSG.PSL3Four.Native CFSG.Sporadic.HeldB CFSG.Sporadic.SmallOddCore
open CFSG.Monster.B.Co2.Native CFSG.Certificates

@[expose] def heU1Tabs (_ : Unit := ()) : Array Tab := Array.ofFn (n := 3) fun i => heRGens[i.val]!

@[expose] def heU2Tabs (_ : Unit := ()) : Array Tab := Array.ofFn (n := 3) fun i => heRGens[i.val + 3]!

@[expose] def heU1Enum (_ : Unit := ()) : Enum := enumBFS 42 (heU1Tabs ()) 8

@[expose] def heU2Enum (_ : Unit := ()) : Enum := enumBFS 42 (heU2Tabs ()) 8

@[expose] def heLiftTab (i : Nat) : Tab := hfCTab (heRWords.getD i [])

@[expose] def heE16SqCheck (_ : Unit := ()) : Bool :=
  comp 8330 (heLiftTab 0) (heLiftTab 0) == idTab 8330 &&
  comp 8330 (heLiftTab 1) (heLiftTab 1) == idTab 8330 &&
  comp 8330 (heLiftTab 2) (heLiftTab 2) == idTab 8330 &&
  comp 8330 (heLiftTab 3) (heLiftTab 3) == idTab 8330 &&
  comp 8330 (heLiftTab 4) (heLiftTab 4) == idTab 8330 &&
  comp 8330 (heLiftTab 5) (heLiftTab 5) == idTab 8330

@[expose] def heE16WithinCheck (_ : Unit := ()) : Bool :=
  let t0 := heLiftTab 0
  let t1 := heLiftTab 1
  let t2 := heLiftTab 2
  let t3 := heLiftTab 3
  let t4 := heLiftTab 4
  let t5 := heLiftTab 5
  let i0 := invTab 8330 t0
  let i1 := invTab 8330 t1
  let i2 := invTab 8330 t2
  let i3 := invTab 8330 t3
  let i4 := invTab 8330 t4
  let i5 := invTab 8330 t5
  commTab 8330 t0 t1 i0 i1 == idTab 8330 &&
  commTab 8330 t0 t2 i0 i2 == idTab 8330 &&
  commTab 8330 t1 t2 i1 i2 == idTab 8330 &&
  commTab 8330 t3 t4 i3 i4 == idTab 8330 &&
  commTab 8330 t3 t5 i3 i5 == idTab 8330 &&
  commTab 8330 t4 t5 i4 i5 == idTab 8330

@[expose] def heE16CrossCheck (_ : Unit := ()) : Bool :=
  let t0 := heLiftTab 0
  let t1 := heLiftTab 1
  let t2 := heLiftTab 2
  let t3 := heLiftTab 3
  let t4 := heLiftTab 4
  let t5 := heLiftTab 5
  let i0 := invTab 8330 t0
  let i1 := invTab 8330 t1
  let i2 := invTab 8330 t2
  let i3 := invTab 8330 t3
  let i4 := invTab 8330 t4
  let i5 := invTab 8330 t5
  commTab 8330 t0 t3 i0 i3 == heT1Arr &&
  commTab 8330 t0 t4 i0 i4 == heT1Arr &&
  commTab 8330 t0 t5 i0 i5 == heT1Arr &&
  commTab 8330 t1 t3 i1 i3 == heT1Arr &&
  commTab 8330 t1 t4 i1 i4 == heT1Arr &&
  commTab 8330 t1 t5 i1 i5 == idTab 8330 &&
  commTab 8330 t2 t3 i2 i3 == idTab 8330 &&
  commTab 8330 t2 t4 i2 i4 == heT1Arr &&
  commTab 8330 t2 t5 i2 i5 == heT1Arr

@[expose] def heCrossPairing : Array (Array Nat) := #[#[1, 1, 1], #[1, 1, 0], #[0, 1, 1]]

@[expose] def heCrossPairingDet (_ : Unit := ()) : Nat :=
  ((heCrossPairing[0]!)[0]! * ((heCrossPairing[1]!)[1]! * (heCrossPairing[2]!)[2]! +
      (heCrossPairing[1]!)[2]! * (heCrossPairing[2]!)[1]!) +
   (heCrossPairing[0]!)[1]! * ((heCrossPairing[1]!)[0]! * (heCrossPairing[2]!)[2]! +
      (heCrossPairing[1]!)[2]! * (heCrossPairing[2]!)[0]!) +
   (heCrossPairing[0]!)[2]! * ((heCrossPairing[1]!)[0]! * (heCrossPairing[2]!)[1]! +
      (heCrossPairing[1]!)[1]! * (heCrossPairing[2]!)[0]!)) % 2

@[expose] def heU1EnumCheck (_ : Unit := ()) : Bool := enumOK 42 (heU1Tabs ()) (heU1Enum ())

@[expose] def heU2EnumCheck (_ : Unit := ()) : Bool := enumOK 42 (heU2Tabs ()) (heU2Enum ())

@[expose] def heU1NormalCheck (_ : Unit := ()) : Bool :=
  normalOK 42 (heU1Enum ()).tabs heXTabs heXInvs (heU1Tabs ())

@[expose] def heU2NormalCheck (_ : Unit := ()) : Bool :=
  normalOK 42 (heU2Enum ()).tabs heXTabs heXInvs (heU2Tabs ())

@[expose] def heU1CentralizerLength (_ : Unit := ()) : Nat :=
  let T := heU1Tabs ()
  (heXEnum.tabs.toList.filter (commAll 42 T)).length

@[expose] def heU2CentralizerLength (_ : Unit := ()) : Nat :=
  let T := heU2Tabs ()
  (heXEnum.tabs.toList.filter (commAll 42 T)).length

end CFSG.ComponentClassification.GrSLit.HeldFix
