module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bOdd
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bOffender

public section

namespace CFSG.QuasithinUnique.Setup.X7b

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Family

theorem noPSp4Component_final
    (hdata : ActualSymplecticFourData) :
    CFSG.QuasithinUnique.Setup.Top.NoPSp4Component :=
  noPSp4Component_of diagram_normalizer_excludes_offenders hdata

end CFSG.QuasithinUnique.Setup.X7b
