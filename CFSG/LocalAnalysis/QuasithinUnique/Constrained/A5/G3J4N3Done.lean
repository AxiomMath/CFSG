module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3J4N3Final
public import CFSG.Sporadic.J4.QT2ABoundT
public import CFSG.Sporadic.J4.QT2ABoundZ

public section

namespace CFSG.QuasithinUnique.A5.G3

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

theorem j4Normalizer3
    : J4Normalizer3 :=
  j4Normalizer3_of_bounds (CFSG.Sporadic.J4.QT2A.card_le_T j4Facts)
    (fun {_} hS hSC {_} hy hy3 hSy => CFSG.Sporadic.J4.QT2A.card_le_Z3 j4Facts
      CFSG.Sporadic.J4.QT2.card_centralizer_eta_three hS hSC hy hy3 hSy)

end CFSG.QuasithinUnique.A5.G3
