module

public import CFSG.LocalAnalysis.ComponentClassification.Foote47Main
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBAschbacherFive
public import CFSG.LocalAnalysis.ComponentClassification.FooteSmallMain
public import CFSG.LocalAnalysis.ComponentClassification.Foote47Gen
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFoote47Central
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFoote47Order

public section

namespace CFSG.ComponentClassification.FooteLit

theorem foote_theorem_4_7 :
    FooteThm47Statement :=
  Foote47.foote_theorem_4_7_of_inputs GSThmB.aschbacherTheorem5Input_holds
      AutL2Facts.footeFourgroupE8 AschbacherKnownGroup.knownGroupFacts_holds
      FooteSmall.footeSmallCentralizers AutL2Facts.footeFourgroupInner
      AutL2Facts.cfFoote47CentralInvolution AutL2Facts.cfFoote47OuterOrderFour
      Foote47.foote47FourgroupGeneration

end CFSG.ComponentClassification.FooteLit
