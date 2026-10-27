module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongE3Sections
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDI278SporCFive
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDI278SporCSeven

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

theorem kdI278SporCNoM_holds
    : KDI278SporCNoM := by
  intro p s hpair hsM Z _ _ K hKn hsK hC B hB hBc hSC W hBW hW
  haveI : K.Normal := hKn
  rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact kdSporC_HS_five hsK hC hB hBc hBW hW
  · exact kdSporC_Ru_five hsK hC hB hBc hBW hW
  · exact kdSporC_Fi24_seven hsK hC hB hBc hBW hW
  · exact kdSporC_He_seven hsK hC hB hBc hBW hW
  · exact kdSporC_ON_seven hsK hC hB hBc hBW hW
  · exact absurd rfl hsM

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
