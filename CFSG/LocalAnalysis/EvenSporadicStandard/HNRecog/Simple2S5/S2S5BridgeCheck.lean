module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.CheckDefs
public import Certificates.Data.HNUnitaryBridge

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Simple2S5

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.EvenSporadicStandard.HNRecog

@[expose] def bridgePts : List ℕ := [
    704, 916, 925, 1059, 1215, 928, 1263, 898, 863, 1000, 1036, 882, 824, 1011, 1391, 1187, 728,
    827, 920, 976, 866, 836, 723, 885, 720, 834, 1023, 992, 803, 718, 1185, 888, 730, 1196,
    1053, 1031, 1033, 726, 927, 793, 997, 1190, 760, 717, 812, 1004, 877, 924, 722, 1272]

@[expose] def bridgeWords : List (List ℕ) := [
  [2, 7, 2, 1, 5, 7, 3, 5, 6, 1, 7, 2, 5, 6, 5, 7, 3, 2, 1, 6, 1],
  [2, 7, 3, 7, 2, 1, 6, 6, 7, 2, 7, 2, 3, 6, 1, 2, 6],
  [3, 7, 4, 7, 5, 4, 6, 1, 2, 5, 7, 2, 7, 6, 3, 1, 3, 6, 7, 2, 7, 2, 3, 1, 2, 6, 1],
  [6, 2, 1, 6, 3, 2, 7, 2, 7, 6, 3, 5, 1, 3, 2, 1, 6, 5, 7, 3, 7, 5, 6, 1],
  [5, 6, 2, 3, 2, 3, 6, 5, 7, 3, 7, 2],
  [5, 2, 1, 6, 7, 1, 7, 1, 2, 3, 2, 1, 3, 1, 2, 3, 7, 5, 6, 5, 7, 3, 6, 1, 2, 1, 6, 5, 1, 6]]

@[expose] def bridgeWordOK (w : List ℕ) (s : Array ℕ) : Bool :=
  let T := tabW w
  ap T 0 == 0 &&
    (List.range 50).all fun l => ap T bridgePts[l]! == bridgePts[s[l]!]!

@[expose] def bridgeOK : Bool :=
  gensOK && bridgeWords.all wordOK && decide (bridgeWords.length = 6) &&
    decide (bridgePts.length = 50) && decide bridgePts.Nodup &&
    bridgePts.all (fun p => decide (p < 1408)) &&
    (List.range 6).all fun k => bridgeWordOK bridgeWords[k]! HNUnitaryBridge.smallPerms[k]!

end CFSG.EvenSporadicStandard.HNRecog.Simple2S5
