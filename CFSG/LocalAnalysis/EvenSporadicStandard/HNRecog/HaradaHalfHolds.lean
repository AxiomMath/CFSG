module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.GH73.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Glue
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.GExists
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.SmallLookup
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.OutputGold
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.OutputMain
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel27.Final
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.SegevSections

public section

namespace CFSG.EvenSporadicStandard.HNRecog

theorem haradaHalf_holds :
    HaradaHalf :=
  Harada.harada_half_of_inputs (setting25Exists_holds GH73.gh73TheoremA64K_holds)
    (Harada.L27.lemma27Exists_of_inputs CFSG.RankThree.PartOne.SPOR.schreierFor_catalog
        Harada.L27.smallSimpleLookup_of_certificates) Harada.goldschmidtTheoremA

theorem haradaHNRecognitionKP_of_segevSections
    (h3 : SegevSection3) (h4 : SegevSection4) (h5 : SegevSection5) :
    TwoHS.HaradaHNRecognitionKP :=
  haradaHNRecognitionKP_of_halves haradaHalf_holds (segevUniqueness_of_sections h3 h4 h5)
    hn_sideFacts

end CFSG.EvenSporadicStandard.HNRecog
