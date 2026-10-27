module

public import CFSG.GH74.GLS.Stage2.Local.GHSchMain
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87NCDProved
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Done
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Final
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31Main
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Psp4A7

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem final_hSch
    : P34.GHSchreier :=
  fun J _ _ _ hn hG => GHSch.ghSchreier_thm J hn hG

theorem final_hfld : ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Stage12.Kind)
    (S : Subgroup G), Stage2Ctx G z k S → Stage1.Main.L4TwoFieldStmt G z k S :=
  fun _ _ _ _ _ _ c => c.detail.l4_two

theorem final_hInv
    : InvSec :=
  invSec_of_secX (secX_proved final_hfld final_hSch)

theorem final_hL31
    : Lemma31Narrow :=
  have h29 : Lemma29First := lemma29First_proved (nonCentralDihedral_of_ctx final_hfld final_hSch)
  leaf_lemma31Narrow_of h29 (lemma29NonSolv_of h29) final_hInv final_hfld final_hSch

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
