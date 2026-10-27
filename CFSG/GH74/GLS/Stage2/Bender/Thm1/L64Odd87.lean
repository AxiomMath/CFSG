module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.L64Final
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Prop42
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpE4Link
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31Main
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Final
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Done

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.L64

open CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Signalizer CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem lemma6_4_of_odd87
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    : Lemma6_4 := by
  have hSch : P34.GHSchreier := fun J _ _ hJ hn hG => by
    have := hJ
    exact GHSch.ghSchreier_thm J hn hG
  have hfld : ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Stage12.Kind) (S : Subgroup G),
      Stage2Ctx G z k S → Stage1.Main.L4TwoFieldStmt G z k S := fun _ _ _ _ _ _ c => c.detail.l4_two
  have hInv : InvSec := invSec_of_secX (secX_proved hfld hSch)
  have h29 : Lemma29First := lemma29First_proved (nonCentralDihedral_of_ctx hfld hSch)
  have h29n : Lemma29NonSolv := lemma29NonSolv_of h29
  have hL31 : Lemma31Narrow := leaf_lemma31Narrow_of h29 h29n hInv hfld hSch
  exact lemma6_4_thm hfld hSch h29
    (prop_4_3E (prop4_2_of_odd87 hGA) hL31)

end CFSG.GH74.GLS.Stage2.Bender.Thm1.L64
