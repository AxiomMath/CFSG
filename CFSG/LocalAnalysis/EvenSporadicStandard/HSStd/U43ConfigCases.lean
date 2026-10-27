module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43ConfigCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43ConfigDataI4
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43ConfigDataZ4
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43ConfigDataVb
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43ConfigDataVa
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43ConfigCheck
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43ConfigDataI4
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43ConfigDataZ4
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43ConfigDataVb
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43ConfigDataVa

public section

namespace CFSG.EvenSporadicStandard.HSStd.U43

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.PairNative
  CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.Schreier.Native CFSG.EvenSporadicStandard.M24Std.CU43
  CFSG.LieType.Multipliers.U43

@[expose] def tabOf (a : Array Nat) : Table := a.map UInt32.ofNat

@[expose] def tabsOf (a : Array (Array Nat)) : Array Table := a.map tabOf

@[expose] def tTab (k : ℕ) : Table := tabOf (tArr k)

@[expose] def gensR : Array Table := #[tabOf tabA, tabOf tabB, tabOf deltaArr, tabOf phiArr]

@[expose] def conjTab (u x : Table) : Table := conjT 820 u (invT 820 u) x

@[expose] def dI4 : CaseData where
  ks := List.range 8
  sizeG := 26127360
  gensG := gensR
  Tt := tabOf reps[4]!
  cg := tabsOf i4Cg
  y0 := tabOf i4Y0
  yg := tabsOf i4Yg
  ysz := 648
  nsol := 0

@[expose] def dI5 : CaseData where
  ks := List.range 8
  sizeG := 26127360
  gensG := gensR
  Tt := tabOf reps[5]!
  cg := (tabsOf i4Cg).map (conjTab (tabOf i5U))
  y0 := conjTab (tabOf i5U) (tabOf i4Y0)
  yg := (tabsOf i4Yg).map (conjTab (tabOf i5U))
  ysz := 648
  nsol := 0

@[expose] def dZ4 : CaseData where
  ks := [0, 1, 2, 3]
  sizeG := 13063680
  gensG := #[tabOf tabA, tabOf tabB, tTab 1]
  Tt := tabOf reps[8]!
  cg := tabsOf z4Cg
  y0 := tabOf z4Y0
  yg := tabsOf z4Yg
  ysz := 1944
  nsol := 12

@[expose] def dVb : CaseData where
  ks := [0, 2, 5, 7]
  sizeG := 13063680
  gensG := #[tabOf tabA, tabOf tabB, tTab 2, tTab 5]
  Tt := tabOf reps[8]!
  cg := tabsOf vbCg
  y0 := tabOf vbY0
  yg := tabsOf vbYg
  ysz := 1944
  nsol := 12

@[expose] def vaCheck : Bool :=
  permOK 820 (tabOf reps[8]!) && permInvOK (tabOf vaZ) && memCos [0, 2, 4, 6] (tabOf vaZ) &&
    commTT 820 (tabOf vaZ) (tabOf reps[8]!) && !tblEq 820 (tabOf vaZ) (idT 820) &&
    !tblEq 820 (tabOf vaZ) (tabOf reps[8]!) &&
    (tabsOf vaCg).all (fun g => memCos [0, 2, 4, 6] g && commTT 820 g (tabOf reps[8]!) &&
      commTT 820 (tabOf vaZ) g) &&
    enumOK (tabsOf vaCg) closureCap 2880

@[expose] def mulIdx (k k' : ℕ) : ℕ :=
  4 * ((k / 4 + k' / 4) % 2) + ((if k' / 4 = 1 then 4 - k % 4 else k % 4) + k' % 4) % 4

@[expose] def dihedralCheck : Bool :=
  (List.range 8).all fun k => (List.range 8).all fun k' =>
    eqA 820 (compA 820 (tArr k) (tArr k')) (tArr (mulIdx k k'))

@[expose] def centCosetCounts : Bool :=
  (List.range 8).all fun k => countW (commW (tArr k) [reps[8]!]) blocks [] == 720

@[expose] def cosetCheck8 : Bool := dihedralCheck && centCosetCounts

end CFSG.EvenSporadicStandard.HSStd.U43
