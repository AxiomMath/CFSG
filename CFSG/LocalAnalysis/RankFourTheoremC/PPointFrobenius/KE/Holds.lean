module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.KE.Families
public import CFSG.HardMathSupport.Malle.SeitzCube.PlanesFinal
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.OrdinaryProofs.MonsterThirteenCubic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Unitary
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentAlt
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentCharPOne
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCharPGen

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.KE

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.LieType.SeitzGeneration


theorem kFactOneLieIdentFive_holds
    : KFactOneLieIdentFive :=
  kFactOneLieIdentFive_of
    (seitzInnerExFive_of_excParabolicFive
      (excParabolicPlaneFive_of_excParabolicPlane
        CFSG.HardMathSupport.Malle.SeitzCube.excParabolicPlane_proved))
    offCharAut oneLieIdentAlt (oneLieIdentLieCharP charPGen)
    (fun s => by
      by_cases hs : s = .M
      · subst hs
        exact oneLieIdentSporAt_M_of_betaData
          CFSG.AGLEmbedding.Norton.OrdinaryProofs.monsterBetaData_of_thirteen_cubic
          (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .M)
      · exact oneLieIdentSporAt_of_ne s hs)

theorem ke_holds
    : KEStatement :=
  ke_psl2_of_abelian_sylow kFactOneLieIdentFive_holds kFactUnitarySylowStructure

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.KE
