module

public import CFSG.CGT.PushingUpLit.C2L.ClassTwoSetupOf
import CFSG.CGT.PushingUpLit.C2L.CfgAssembly
import CFSG.CGT.PushingUpLit.C2L.Gomi46DataOf
import CFSG.CGT.PushingUpLit.C2L.PhaseLSecond
import CFSG.CGT.PushingUpLit.T2KSW.NonsplitWC

public section

namespace CFSG.CGT.PushingUpLit.C2L

open CFSG CFSG.ABGLocalTools CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.T2K
  CFSG.CGT.PushingUpLit.T2KSW CFSG.CGT.Timmesfeld75
open CFSG.EvenSporadicStandard.Finkelstein77 (Asc76Lemma25)

theorem phaseL_of_inputs
    (hE1 : FooteNonsolvableSimple) (hE8 : SolomonTimmesfeldTight) (h25 : Asc76Lemma25)
    (hSCL : SimpleCaseListStmt) (hList : ListWCIdentification) (hA78 : Aschbacher78OneGen) :
    PhaseL := by
  refine phaseL_of_secondBlockInput hE1 ?_
  intro G _ _ L M T n hs hE hcl hnwc
  have hc : ClassTwoSetup G L M T n :=
    classTwoSetup_of hE1 hE8 h25 hSCL hList hA78 hs hE hcl hnwc
  have hWVE : oTwoIn L ≤ blockU L ⊔ Ec L T :=
    wleVE_of_Rl_sup_Dc hE1 hE8 h25 hSCL hList hs hE hc.hRD
  have h46 : Gomi46Data G :=
    gomi46Data_of_ambient (hc.gomiAmbient hWVE) hc.oddCore_eq_bot hc.pCore_eq_bot
  obtain ⟨D₂, a, hin⟩ := hc.exists_secondBlockInput hWVE h46
  exact ⟨_, D₂, a, hin⟩

end CFSG.CGT.PushingUpLit.C2L
