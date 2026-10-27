module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Inputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Data3
public import CFSG.Sporadic.SmallOddCore.CentData
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Inputs
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Data3
public meta import Certificates.Data.CFSGNative.SmallOddCore.Check
public meta import CFSG.Sporadic.SmallOddCore.CentData

public section

namespace CFSG.EvenSporadicStandard.M24Std.CU43

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

@[expose] def sylTabs : Array Table :=
  #[sylGen0, sylGen1, sylGen2, sylGen3, sylGen4].map fun a => a.map UInt32.ofNat

@[expose] def sylCap : ℕ := 256

@[expose] def sylEnum : Array Table × Array ℕ × Array ℕ := mulClosureH 820 sylTabs sylCap

@[expose] def sylPermCheck : Bool :=
  sylTabs.all fun x => permOK 820 x && CFSG.Sporadic.Th.Native.invOK 820 x (invT 820 x)

@[expose] def sylInPCheck : Bool := sylTabs.all fun x => inP (natArr x)

@[expose] def sylEnumCheck : Bool :=
  mulTreeOK 820 sylTabs sylEnum.1 sylEnum.2.1 sylEnum.2.2 &&
    closedOK 820 (sylTabs ++ sylTabs.map (invT 820)) sylEnum.1 &&
    hkeysDistinct 820 sylEnum.1.toList && sylEnum.1.size == 128

@[expose] def rankCheck : Bool :=
  decide
    (((Finset.range 128).filter fun i =>
        ∀ j < 128, commTT 820 sylEnum.1[i]! sylEnum.1[j]! = true).card ≤ 16 ∧
      ∀ i < 128, involOK 820 sylEnum.1[i]! = true →
        (∃ j < 128, commTT 820 sylEnum.1[i]! sylEnum.1[j]! = false) →
          ((Finset.range 128).filter fun j =>
            involOK 820 sylEnum.1[j]! = true ∧
              commTT 820 sylEnum.1[i]! sylEnum.1[j]! = true).card ≤ 30)

end CFSG.EvenSporadicStandard.M24Std.CU43
