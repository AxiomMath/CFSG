module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitCaseK
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2Act
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2S3Main
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKDBase
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKDA6
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec5E
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec5HMain
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitFinal

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG

theorem fritzA7Sections4to8_of_812 (h812 : Sec8.Fritz812dNotSylowInput) : FritzA7Sections4to8 :=
  fritzA7Sections4to8_of_parts fritzA7Section4
    (fritzA7Section5_of_parts fritzA7Section5Data fritzA7Section5E fritzA7Section5H)
    fritzA7Section6 fritzA7Section7 (Sec8.fritzA7Section8_of_input h812)

theorem fritzTheoremB_of_steps (hH : HaradaInput) (hGH : GorensteinHarrisInput)
    (hB : GHPresentationBound) (hM : GHRelInHS) (h812 : Sec8.Fritz812dNotSylowInput)
    (h36 : FritzL2Lemma36Final) (h378 : FritzL2Lemma378) (hKD : FritzKDSylow) :
    FritzTheoremB :=
  fritzTheoremB_of_parts hH hGH (fritzA7Sections4to8_of_812 h812) fritzL2Action
    (fritzL2Section3_of_parts h36 h378) fritzL2CaseK (fritzL2CaseKD_of_parts hB hM hKD hsQuotA6)

theorem hsflit_of_steps (hGH74 : UFrontier.GH74ModelsInput) (hH : HaradaInput)
    (hGH : GorensteinHarrisInput) (hB : GHPresentationBound) (hM : GHRelInHS)
    (h812 : Sec8.Fritz812dNotSylowInput) (h36 : FritzL2Lemma36Final) (h378 : FritzL2Lemma378)
    (hKDF : FritzL2KDFacts) (h4 : FritzKDSection4) (h6 : FritzKDSection6)
    (h7 : FritzKDSection7) (h8ab : FritzKDSection8ab) (h8c : FritzKDSection8c) :
    GSLit.HarrisSolomonFritzInput :=
  hsflit_of_inputs hGH74 (fritzTheoremB_of_steps hH hGH hB hM h812 h36 h378
    (fritzKDSylow_of_parts hKDF h4 h6 h7 h8ab h8c))

end CFSG.ComponentClassification.HSFLit
