module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Alt
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FSporAll
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FMcLyCC
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Two
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P85gMain
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P85eMain
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL2Main
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3Main
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU3Main
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FSp4Final
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FG2SMain
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FD4SMain
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87G2ThreeMax
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L4SvThm
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvThm
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU5
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FRee
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Psp4A7
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87MultMilestone
public import CFSG.GH74.Generic.GKFFinal
public import CFSG.GH74.GLS.Stage2.Signalizer.Prop41
public import CFSG.GH74.GLS.Stage2.Signalizer.L199
public import CFSG.GH74.GLS.Stage2.Local.GHSchMain

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Bg

theorem prop4_2_of_odd87
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    : Prop4_2 := by
  have hSch : P34.GHSchreier := fun J _ _ hJ hn hG => by
    have := hJ
    exact GHSch.ghSchreier_thm J hn hG
  have hfld : ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G),
      Stage2Ctx G z k S → Stage1.Main.L4TwoFieldStmt G z k S := fun _ _ _ _ _ _ c => c.detail.l4_two
  have hInv : InvSec := invSec_of_secX (secX_proved hfld hSch)
  have hL34 : L34Aut := l34Aut_of_model l34AutOn_psl3Four
  have hF : Generic.GenericKnownFacts := Generic.genericKnownFacts_of_griess hGA
  have hMult3 : G2ThreeMult := g2ThreeMult_of_milestone hGA
  have hD4 : D4Mult := d4Mult_of_milestone hGA
  exact prop4_2_of_cells cell87_FAlt
    cell87_FSpor_cert cell87_FMcLy_cert
    (cell87_FTwo prop85e_thm prop85g_thm hL34 hInv) (cell87_FL2 hF) cell87_FL3 (cell87_FU3 hF)
    (cell87_FSp4_thm hInv) (cell87_FG2_S g2ThreeMax_of_cert hMult3) (cell87_FD4_S hD4) (cell87_FL4 hInv l4SurvCore_thm)
    (cell87_FU4 hInv u4SurvCore_thm) cell87_FL5 cell87_FU5 cell87_FRee (prop_4_1a_of L199.ig_19_9) (prop_4_1b_of L199.ig_19_9)

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
