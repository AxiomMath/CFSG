module

public import CFSG.LocalAnalysis.RankThreeUC.K37HGKit
public import CFSG.LieType.SeitzGeneration.QuasiHigh5UnitaryEight
public import CFSG.LocalAnalysis.RankThreeUC.K37HDefs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K37H

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC.S15.K37

theorem k37Rest₂U38_holds :
    K37Rest₂U38 := by
  intro X _ _ K E S hs hO
  exfalso
  obtain ⟨⟨d, hv⟩, ⟨-, -, ⟨e⟩⟩, m, q, hd, hm, h8, -⟩ := hO
  obtain rfl : d = .twistedA m q := hd
  subst hm
  exact k37G_false_of_forall_seitzHyperGamma hs fun A hA hA9 =>
    CFSG.LieType.SeitzGeneration.QuasiHigh5.seitzHyperGamma_eq_top_unitary_eight
      (k37G_isQuasisimple_open hs) e h8 hA hA9

end CFSG.LocalAnalysis.RankThreeUC.S15.K37H

end
