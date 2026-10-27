module

public import CFSG.GH74.QTGen4.Recog.G23.Words
public import Certificates.Certificate320008
public meta import CFSG.Certificates.CosetTablePresented
public meta import CFSG.GH74.QTGen4.Recog.G23.Words

public section

namespace CFSG.GH74.QTGen4.Recog.G23

open CFSG.CosetTable


theorem g23H5_check :
    Finite (PG (subsetOf 6 [0, 1, 2, 3, 4]).length g23H5) ∧
      Nat.card (PG (subsetOf 6 [0, 1, 2, 3, 4]).length g23H5) ≤ 576 :=
  Certificates.certificate320008

theorem g23H5_card_le :
    Finite (PG (subsetOf 6 [0, 1, 2, 3, 4]).length g23H5) ∧
      Nat.card (PG (subsetOf 6 [0, 1, 2, 3, 4]).length g23H5) ≤ 576 :=
  g23H5_check

end CFSG.GH74.QTGen4.Recog.G23
