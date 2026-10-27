module

public import CFSG.CGT.PushingUpLit.T2KSW.Print55
public import CFSG.CGT.PushingUpLit.C2L.Defs
import CFSG.CGT.PushingUpLit.C2L.Phase0
import CFSG.CGT.PushingUpLit.C2L.PhaseL

public section

namespace CFSG.CGT.PushingUpLit.C2L

open CFSG CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.T2K CFSG.CGT.PushingUpLit.T2KSW
  CFSG.CGT.Timmesfeld75
open CFSG.EvenSporadicStandard.Finkelstein77 (Asc76Lemma25)

theorem print55ClassTwo_of_inputs
    (hE1 : FooteNonsolvableSimple) (hE8 : SolomonTimmesfeldTight) (h25 : Asc76Lemma25)
    (hSCL : SimpleCaseListStmt) (hList : ListWCIdentification) (hA78 : Aschbacher78OneGen)
    (hP : A78SylowSp4) : Print55ClassTwo :=
  print55ClassTwo_of_phases (phase0_of hE1 hE8 h25 hSCL hList)
    (phaseL_of_inputs hE1 hE8 h25 hSCL hList hA78) hP

theorem print55_of_sylowSp4
    (hE1 : FooteNonsolvableSimple) (hE8 : SolomonTimmesfeldTight) (h25 : Asc76Lemma25)
    (hSCL : SimpleCaseListStmt) (hList : ListWCIdentification) (hA78 : Aschbacher78OneGen)
    (hP : A78SylowSp4) : T2K.Print55 :=
  print55_of_split (print55ClassTwo_of_inputs hE1 hE8 h25 hSCL hList hA78 hP)
    (print55ClassThree_of_inputs hE1 hE8 h25 hSCL hList hA78)

end CFSG.CGT.PushingUpLit.C2L
