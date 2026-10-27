module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28ClosedTransport
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28ClosedFocal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

theorem kFactL28Closed_holds (h12 : KFactL28ThreeQuotient) (hC : KFactOutThreeCoprime)
    (hN : KFactOutThreeNilpotent) : KFactL28Closed := by
  intro G _ _ M P x k hc
  obtain ⟨P', x', k', hd⟩ := GL83P3L28Cl.exists_closedData hc
  refine GL83P3L28Cl.exists_normal_of_pCore_ne_bot M fun hbot => ?_
  exact hd.false_of_setting ⟨hd.sylow, hd.shape, GL83P3L28Red.core_red, hbot⟩ h12 hC hN

end CFSG.LocalAnalysis.RankThreeTheoremC
