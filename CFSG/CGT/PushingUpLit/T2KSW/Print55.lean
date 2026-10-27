module

public import CFSG.CGT.PushingUpLit.T2KSW.Defs
public import CFSG.CGT.PushingUpLit.T2KR.Asc78Gen
public import CFSG.CGT.Timmesfeld75.SimpleCase
public import CFSG.CGT.Timmesfeld75.StdPair
import CFSG.CGT.PushingUpLit.T2KSW.FieldAutNonsplit
import CFSG.CGT.PushingUpLit.T2KSW.NonsplitWC
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.CGT.PushingUpLit.T2KSW

open CFSG CFSG.ABGLocalTools CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.T2K
open CFSG.EvenSporadicStandard.Finkelstein77 (Asc76Lemma25)

theorem print55ClassThree_of_inputs
    (hE1 : FooteNonsolvableSimple) (hE8 : SolomonTimmesfeldTight) (h25 : Asc76Lemma25)
    (hSCL : CFSG.CGT.Timmesfeld75.SimpleCaseListStmt)
    (hList : CFSG.CGT.Timmesfeld75.ListWCIdentification) (hA78 : Aschbacher78OneGen) :
    Print55ClassThree := by
  intro G _ _ L M T n hs hE hnc
  have hRD := t_le_rd_all hs hE1 hA78 hE
  exact false_of_classThree' hE1 hE8 h25 hSCL hList hs hE hnc
    (wleVE_of_Rl_sup_Dc hE1 hE8 h25 hSCL hList hs hE hRD) hRD

end CFSG.CGT.PushingUpLit.T2KSW
