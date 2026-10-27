module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmTwoDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKFSporBZ

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKF

theorem kdI278SporB_holds :
    KDI278SporB := by
  intro p s hpair Z _ _ K hKn hsK hC _
  haveI : K.Normal := hKn
  right
  intro B U _ hB _ hU
  obtain ⟨eK⟩ := hsK
  rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact kdSporB_Th K eK hC B U hB hU
  · exact kdSporB_Co2 K eK hC B U hB hU
  · exact kdSporB_Co3 K eK hC B U hB hU
  · exact kdSporB_McL K eK hC B U hB hU
  · exact kdSporB_J4 K eK hC B U hB hU

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
