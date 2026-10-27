module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134Native
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134Families
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyOddRankOneGlue

public section

namespace CFSG.QuasithinUnique.Vol2Native

theorem a134RankOneFact
    : A134RankOneFact :=
  a134RankOneFact_of_triality Setup.Family.trialityTwoHasRankTwo

theorem a134SQTKFactCat
    : A134SQTKFactCat :=
  a134SQTKFactCat_of_rankOne a134RankOneFact

end CFSG.QuasithinUnique.Vol2Native
