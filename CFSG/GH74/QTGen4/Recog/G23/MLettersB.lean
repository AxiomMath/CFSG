module

public import CFSG.GH74.QTGen4.Recog.G23.Words
public import Certificates.Certificate320006
public meta import CFSG.GH74.QTGen4.Recog.G23.Words

public section

namespace CFSG.GH74.QTGen4.Recog.G23

open CFSG.CosetTable


theorem g23PM_subgroup_closes :
    (genSub {r : FreeGroup (Fin 3) | r ∈ g23PM.map FreeGroup.mk} (subsetOf 3 [0, 1])).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin 3) | r ∈ g23PM.map FreeGroup.mk} (subsetOf 3 [0, 1])).index ≤ 7 :=
  Certificates.certificate320006

end CFSG.GH74.QTGen4.Recog.G23
