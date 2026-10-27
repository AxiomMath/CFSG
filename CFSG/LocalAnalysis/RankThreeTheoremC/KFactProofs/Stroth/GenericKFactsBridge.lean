module

public import CFSG.Yardstones.M9cbf837c48cf.Definitions
public import CFSG.Yardstones.Mdac756b924db.Definitions

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth

theorem gl83GenericKFacts_of_statement
    (h : CFSG.Yardstones.M9cbf837c48cf.GL83GenericKFactsStatement) :
    CFSG.Yardstones.Mdac756b924db.GL83GenericKFacts := by
  obtain ⟨hK2, hTwo, hTriv, hWC, hIA, hU3, hCP, hL34U, hL34B, hL34G, hBal, hZJ, hAS⟩ := h
  exact ⟨hK2, hTwo, hBal, hZJ, hAS, hCP, hTriv, hWC, hIA, hU3, hL34U, hL34B, hL34G⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth
