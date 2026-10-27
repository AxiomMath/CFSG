module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256q2
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxTriality
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExcTw2

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.GF4Rest3

open CFSG.LocalAnalysis.GLTheoremA

set_option linter.unusedSectionVars false


@[expose] def GF4CompsRest3 : Prop :=
  Inputs256q.TwoEltLayerRest ∧ KD264Lie.LieCompIdx KD264Lie.isExcUntwistedIdx ∧ KD264Lie.TwistedE6RationalCatalogue

theorem gf4CompsRest2_of_rest3 (h : GF4CompsRest3) : Inputs256p.GF4CompsRest2 :=
  Inputs256q.gf4CompsRest2_of_rest h.1
    ⟨KD264Lie.lieCompIdx_triality, h.2.1, KD264Lie.lieCompIdx_excTwisted_of_rational h.2.2⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.GF4Rest3

end
