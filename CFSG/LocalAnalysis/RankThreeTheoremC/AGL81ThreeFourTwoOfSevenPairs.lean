module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoLinTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoUnitary
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoSpFour
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoLinThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoReeTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoThreeLie
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoThreePairs
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoThreeAlt
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoThreeSpor
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoLTwoEightSq
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoFive
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoAltTen
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoSzSq
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoCases
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoSporNone
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoHS

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen


theorem threeFourTwoSporadicPairs_of
    (hON : ThreeFourTwoAt 7 (TauCeti.CFSGIndex.sporadic .ONan).Group)
    (hFi : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group →
      ThreeFourTwoAt 7 (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group) :
    ThreeFourTwoSporadicPairs :=
  ⟨threeFourTwoAt_hs, fun s hs hk => by
    rcases hs with rfl | rfl
    · exact hON
    · exact hFi hk⟩

theorem kFactThreeFourTwo_of_sevenPairs
    (hON : ThreeFourTwoAt 7 (TauCeti.CFSGIndex.sporadic .ONan).Group)
    (hFi : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group →
      ThreeFourTwoAt 7 (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group) :
    KFactThreeFourTwo :=
  kFactThreeFourTwo_of_cases threeFourTwoLinTwo_holds threeFourTwoUnitary_holds
      threeFourTwoSpFour_holds threeFourTwoLinThree_holds threeFourTwoReeTwo_holds
      threeFourTwoThreeLie_holds threeFourTwoThreePairs_holds threeFourTwoThreeAlt_holds
      threeFourTwoThreeSporadic_holds threeFourTwoLTwoEightSq_holds threeFourTwoFiveLie_holds
      threeFourTwoAltTen_holds threeFourTwoSporadicNone_holds (threeFourTwoSporadicPairs_of hON hFi)
      threeFourTwoSzSq_holds

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
