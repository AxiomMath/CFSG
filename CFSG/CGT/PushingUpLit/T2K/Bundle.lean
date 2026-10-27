module

public import CFSG.CGT.PushingUpLit.T2K.Final

public section

namespace CFSG.CGT.PushingUpLit.T2K

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS
open CFSG.EvenSporadicStandard.Finkelstein77 (Asc76Lemma25)

structure OpenInputs : Prop where
  asc78 : Aschbacher78OneGen
  hall : Asc76Lemma25
  print55 : Print55

theorem aschbacherTheoremTwoK_of_bundle (hB : OpenInputs) (hE1 : FooteNonsolvableSimple)
    (hE2 : SolomonAlternatingBlockK) (hST : SolK.SolomonTimmesfeldTight)
    (hOrd : SolK.TightSmallGroupOrders) (hGold : CFSG.CGT.Timmesfeld75.Goldschmidt1974)
    (hbhs : BHSLocalCStar) (h616 : CFSG.CGT.PushingUpLit.CGT6.AschbacherSixSixteenNormal)
    (hCoreNat : CFSG.CGT.PushingUpLit.CGT6.AschbacherSixThreeCoreNat)
    (hBS : T2KR.P53.BenderSuzukiStatement) (hL214 : CFSG.CGT.Timmesfeld75.Lemma214)
    (hSz : T2KR.SzTwoPointTorus) (hSCL : CFSG.CGT.Timmesfeld75.SimpleCaseListStmt)
    (hList : CFSG.CGT.Timmesfeld75.ListWCIdentification) : AschbacherTheoremTwoK :=
  aschbacherTheoremTwoK_of_inputs hE1 hE2 hB.asc78 hST hOrd hB.hall hGold hbhs h616 hCoreNat hBS
    hB.print55 hL214 hSz hSCL hList

end CFSG.CGT.PushingUpLit.T2K
