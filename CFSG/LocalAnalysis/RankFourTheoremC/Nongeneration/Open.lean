module

public import CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.D1Inputs
public import CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.I2316.Final
public import CFSG.LieType.SeitzGeneration.OmegaF2.Plus
public import CFSG.LieType.SeitzGeneration.OmegaF2.Minus

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

theorem gl83I241_of_aniN
    (hAniN :
      CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.SeitzExcAnisotropicNotG2ThreePlus) :
    GL83I241 := by
  have hEx : CFSG.LieType.SeitzGeneration.KFactSeitzRankTwoInnerEx :=
    CFSG.HardMathSupport.Malle.SeitzCube.kFactSeitzRankTwoInnerEx_of_anisoN hAniN
  have hB7 := CFSG.AGLEmbedding.sporGammaOneAt_B_seven
  have hβM := CFSG.AGLEmbedding.Norton.OrdinaryProofs.monsterBetaData_of_thirteen_cubic
  have hbr := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  have hMcard := CFSG.Milestones.fam_m_finiteness
  have h11 := CFSG.AGLEmbedding.Norton.sporGammaOneAt_M_eleven_holds
  have h13 := CFSG.AGLEmbedding.Norton.sporGammaOneAt_M_thirteen_holds
  have hMSI := CFSG.AGLEmbedding.smallIdentSporAt_M_of_betaData hβM (hbr .M) hMcard h11 h13
  have hMOL := CFSG.AGLEmbedding.oneLieIdentSporAt_M_of_betaData hβM (hbr .M)
  have hSI : CFSG.AGLEmbedding.KFactSmallIdent :=
    CFSG.LieType.SeitzGeneration.kFactSmallIdent_of_seitzEx hEx hB7 hMSI
  have hOL : CFSG.AGLEmbedding.KFactOneLieIdent :=
    CFSG.LieType.SeitzGeneration.kFactOneLieIdent_of_seitzEx hEx hMOL
  have h241 : GL83I241 := And.intro hSI hOL
  exact h241

theorem gl83NongenerationList_of_open

    (hAniN :
      CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.SeitzExcAnisotropicNotG2ThreePlus)
    (hXC : CFSG.AGLEmbedding.SeitzCyc.SeitzExcOuterCycResiduals)
    (h243 : GL83ComponentPCoreTrivial) : GL83NongenerationList := by
  exact gl83NongenerationList_of_d1Inputs hAniN
    CFSG.LieType.SeitzGeneration.subfieldPairOmegaPlusF2_holds
    CFSG.LieType.SeitzGeneration.subfieldPairOmegaMinusF2_holds hXC h243
    (Nongeneration.I2316.gl83I2316_of_gl83I241 (gl83I241_of_aniN hAniN))

end CFSG.LocalAnalysis.RankFourTheoremC
