module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBOuter
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResModels

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup

theorem chevTwoDiagonalTwoPartCentralized_holds : ChevTwoDiagonalTwoPartCentralized := by
  intro X _ _ L _ hs hnab hcat hnalt hCL hE hrk hchev hL3 D hDel hDcard hDL hcase d hd hd1 S hSR
    hS2 hDS
  have hd3 : d ^ 3 = 1 := hDel.2 d hd
  have hSbot : S = ⊥ := eq_bot_of_lThreeTwo hCL hE hrk hL3 hd3 hSR hS2
  rw [hSbot]
  exact Subgroup.commutator_bot_left D

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
