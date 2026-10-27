module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.OrdinaryProofs.MonsterCaseThreeFiveThirteen
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.OrdinaryProofs.MonsterGammaCoreTwo
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.OrdinaryProofs.MonsterGammaFromGmat
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.OrdinaryProofs.OddLocalAssembly
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON11_13.D13Core
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON11_13.ElevenFusion
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.SevenMonster

public section

namespace CFSG.AGLEmbedding.Norton

theorem monsterCaseThreeData_holds :
    CFSG.AGLEmbedding.MonsterCaseThreeData := by
  have : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M) :=
    OrdinaryProofs.carrier_M_simple
  exact OrdinaryProofs.monsterCaseThreeData_of_five_thirteen
    (MON5_7.sporCaseThreePrimeData_seven_of_monster (MulEquiv.refl _))

theorem sporGammaOneAt_M_eleven_holds :
    CFSG.AGLEmbedding.SporGammaOneAt .M 11 := by
  have : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M) :=
    OrdinaryProofs.carrier_M_simple
  obtain ⟨e⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple
    (MulEquiv.refl (CFSG.Blueprint.NativeSporadic.Carrier .M))
  exact OrdinaryProofs.sporGammaOneAt_M_eleven_of_gmat e
    MON11_13.fusionGenerationOf_gmat_eleven

theorem sporGammaOneAt_M_thirteen_holds :
    CFSG.AGLEmbedding.SporGammaOneAt .M 13 := by
  have : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M) :=
    OrdinaryProofs.carrier_M_simple
  obtain ⟨e⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple
    (MulEquiv.refl (CFSG.Blueprint.NativeSporadic.Carrier .M))
  exact OrdinaryProofs.sporGammaOneAt_M_thirteen_of_core_two e
    MON11_13.glbCore_two_thirteen_gmat

theorem d2IndexCaseAt_M_seven_eleven_thirteen_holds :
    CFSG.AGLEmbeddingD2.D2IndexCaseAt (.sporadic .M) fun p => p = 7 ∨ p = 11 ∨ p = 13 :=
  OrdinaryProofs.d2IndexCaseAt_M_of_gmat_inputs MON11_13.fusionGenerationOf_gmat_eleven
    MON11_13.glbCore_two_thirteen_gmat

end CFSG.AGLEmbedding.Norton
