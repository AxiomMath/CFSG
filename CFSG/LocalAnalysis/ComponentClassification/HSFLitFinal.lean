module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitTop
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Top
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitEvenLie
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitSporadic
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec4
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7S5Main
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec6
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec7Main
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG

theorem hsflit_of_inputs (hGH : UFrontier.GH74ModelsInput) (hB : FritzTheoremB) :
    GSLit.HarrisSolomonFritzInput :=
  hsflit_of_parts hGH excluded_of_even_items excluded_of_sporadic_items hB

theorem harris_solomon_fritz_A7_of_inputs (hGH : UFrontier.GH74ModelsInput) (hH : HaradaInput)
    (h5E : FritzA7Section5E) (h5H : FritzA7Section5H) (h812 : Sec8.Fritz812dNotSylowInput) :
    GSLit.HarrisSolomonFritzA7Input :=
  harris_solomon_fritz_A7_of_parts hGH excluded_of_even_items excluded_of_sporadic_items hH
    (fritzA7Sections4to8_of_parts fritzA7Section4
      (fritzA7Section5_of_parts fritzA7Section5Data h5E h5H) fritzA7Section6 fritzA7Section7
      (Sec8.fritzA7Section8_of_input h812))

end CFSG.ComponentClassification.HSFLit
