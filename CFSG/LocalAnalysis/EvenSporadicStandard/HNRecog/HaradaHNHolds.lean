module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Dichotomy
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.Holds
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.FieldMemQ
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.FieldRankTwo
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.FieldInvClasses
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.FieldThreeLocal
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.FieldFiveShapes
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.FieldFiveLocal
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.FieldCentBase
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.FieldCentInv
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.FieldHyp3
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaHalfHolds
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Assembly
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Segev27Proof
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.M11Final
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.SegevSection4Holds
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5Main

public section

namespace CFSG.EvenSporadicStandard.HNRecog

theorem segevSection3_holds :
    SegevSection3 :=
  fun _ _ _ _ _ _ h => Section3.f5Local_of_isF5Type twoHSInterface
    (Section3.suborbitFacts_of_simple_2S5 Simple2S5.simple2S5_holds)
        ({ mem_Q_of_cent := Section3.cSideFacts_mem_Q_of_cent,
           rank_two := Section3.cSideFacts_rank_two,
           inv_classes := Section3.cSideFacts_inv_classes,
           three_local := Section3.cSideFacts_three_local,
           five_local_shapes := Section3.cSideFacts_five_local_shapes,
           five_local := Section3.cSideFacts_five_local,
           centQ_inv_base := Section3.cSideFacts_centQ_inv_base,
           centQ_inv := Section3.cSideFacts_centQ_inv,
           hyp3_of_free := Section3.cSideFacts_hyp3_of_free })
    Section3.m11Facts_holds Section3.u35Facts_holds aschbacherDichotomy Section3.segev27_holds h

theorem haradaHNRecognitionKP_holds :
    TwoHS.HaradaHNRecognitionKP :=
  haradaHNRecognitionKP_of_segevSections segevSection3_holds Section4.segevSection4_holds
    AutGamma.segevSection5_holds

end CFSG.EvenSporadicStandard.HNRecog
