module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Final3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3SporRu

public section

namespace CFSG.QuasithinUnique.A5.G3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native

theorem Delta5Residual7.of_j4
    (hj4 : J4Normalizer3) : Delta5Residual7 where
  j4 := hj4
  ru := fun _ _ _ _ hX => noDelta5In_ru hX

theorem a314A5Excluded_direct8
    (hT : ThreeCoverFactCat) (hcore : A36CoreForSQTKCat)
    (h37 : A37ForSQTKCat) (h39 : A39ForSQTKCat) (hj4 : J4Normalizer3) : A314A5Excluded :=
  a314A5Excluded_direct7 hT hcore h37 h39 (Delta5Residual7.of_j4 hj4)

end CFSG.QuasithinUnique.A5.G3
