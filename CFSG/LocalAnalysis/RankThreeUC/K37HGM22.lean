module

public import CFSG.LocalAnalysis.RankThreeUC.K37HGKit
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.K35CentralM22
public import CFSG.LocalAnalysis.RankThreeUC.K37HDefs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K37H

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC.S15.K37

theorem k37Rest₁₀_holds :
    K37Rest₁₀ := by
  intro X _ _ K E S hs hO
  exfalso
  obtain ⟨-, -, ⟨e⟩⟩ := hO
  exact k37G_false_of_forall_seitzHyperGamma hs fun A hA hA9 =>
    CFSG.LocalAnalysis.AGL81TheoremCD.Section14.K35Central.seitzHyperGamma_eq_top_of_m22
      (k37G_isQuasisimple_open hs) (k37G_isPGroup_center hs) e hA hA9

end CFSG.LocalAnalysis.RankThreeUC.S15.K37H

end
