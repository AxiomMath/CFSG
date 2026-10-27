module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitFinal
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec5E
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec5HMain

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG

theorem hsflitA7_of_inputs (hGH : UFrontier.GH74ModelsInput) (hH : HaradaInput)
    (h812 : Sec8.Fritz812dNotSylowInput) : GSLit.HarrisSolomonFritzA7Input :=
  harris_solomon_fritz_A7_of_inputs hGH hH fritzA7Section5E fritzA7Section5H h812

end CFSG.ComponentClassification.HSFLit
