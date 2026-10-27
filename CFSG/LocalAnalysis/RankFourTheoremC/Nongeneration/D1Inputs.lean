module

public import CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.Main
public import CFSG.LocalAnalysis.GL83PartI.I713.Final
public import CFSG.HardMathSupport.Malle.SeitzCube.InnerExFrontier
public import CFSG.LieType.SeitzGeneration.ConsumerEx
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzCyc.D1
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MonsterTargets

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

theorem gl83NongenerationList_of_d1Inputs
    (hAniN :
      CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.SeitzExcAnisotropicNotG2ThreePlus)
    (hOP : CFSG.LieType.SeitzGeneration.SubfieldPairOmegaPlusF2)
    (hOM : CFSG.LieType.SeitzGeneration.SubfieldPairOmegaMinusF2)
    (hXC : CFSG.AGLEmbedding.SeitzCyc.SeitzExcOuterCycResiduals)
    (h243 : GL83ComponentPCoreTrivial) (h2316 : GL83I2316) : GL83NongenerationList := by
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
  have hSz : CFSG.AGLEmbedding.KFactSeitzCyc :=
    CFSG.AGLEmbedding.SeitzCyc.kFactSeitzCyc_of_pairs_cyc hOP hOM hXC
  have h241 : GL83I241 := And.intro hSI hOL
  exact gl83NongenerationList_of_kfacts h243 h241 GL83.I713.i_7_13_1_holds hSz h2316

end CFSG.LocalAnalysis.RankFourTheoremC
