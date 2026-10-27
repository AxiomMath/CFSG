module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3J4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3J4N3

public section

namespace CFSG.QuasithinUnique.A5.G3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem j4Normalizer3_of_bounds
    (hT : J4N3.BoundT) (hZ : J4N3.BoundZ) : J4Normalizer3 :=
  fun _ _ _ hX P N hP hN => J4N3.normalizer3_of_bounds hT hZ hX P N hP hN

end CFSG.QuasithinUnique.A5.G3
