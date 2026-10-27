module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.DataLocalOfUnique
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.DataLocalUnique

public section

namespace CFSG.EvenSporadicStandard.J4Std

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

theorem localData_J4
    {G : Type} [Group G] (ι : CFSG.Sporadic.J4.J →* G) (hι : Function.Injective ι) :
    LocalData ι.range ((Eg uJ 11).map ι) (P0.map ι) :=
  localData_J4_of_unique ι hι fun _ hA hsq hcomm hcard =>
    DataLocal.unique_J j4Facts hA hsq hcomm hcard

end CFSG.EvenSporadicStandard.J4Std
