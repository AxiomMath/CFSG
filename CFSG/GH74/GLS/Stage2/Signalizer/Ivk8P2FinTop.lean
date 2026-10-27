module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2FinCells
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S1
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S2L2
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S2L7
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S3
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4L182Thm
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4L3
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4L4
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4a
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4K2QMain
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4L6Top
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S5P181T
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8K0Main
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KBMain
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KBCert
public import CFSG.GH74.GLS.Stage2.Local.P34Final
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87NCDProved
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Done
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Final
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31Main
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Psp4A7
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL3
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAU4Final

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.GH74.GLS.Stage2.Signalizer.Odd87


theorem prop18_13_of_cells (hcov : PSp4_oddCover) (kL3 : KAY FL3) (kU4 : KAY FU4) :
    Prop18_13 := by
  have h34 : Leaf_Prop34 := P34.leaf_prop34_proved
  have hSch : P34.GHSchreier := fun J _ _ _ hn hG => GHSch.ghSchreier_thm J hn hG
  have hfld : ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Stage12.Kind) (S : Subgroup G),
      Stage2Ctx G z k S → Stage1.Main.L4TwoFieldStmt G z k S :=
    fun _ _ _ _ _ _ c => c.detail.l4_two
  have hND : NonCentralDihedral := nonCentralDihedral_of_ctx hfld hSch
  have h29 : Lemma29First := lemma29First_proved hND
  have hInv : InvSec := invSec_of_secX (secX_proved hfld hSch)
  have hL31 : Lemma31Narrow :=
    leaf_lemma31Narrow_of h29 (lemma29NonSolv_of h29) hInv hfld hSch
  have h171 : Prop17_1 := CFSG.GH74.GLS.Stage2.Final.Thm4.prop17_1 h34 hcov
  have hKA2 : IVK_8_13_two := ivk_8_13_two_of_narrow hL31
  have hAB : IG_11_7 := ig_11_7_thm
  have h1123 : IG_11_23 := ig_11_23_thm
  have h172 : Lemma17_2 := P2S2.lemma17_2_of hL31
  have h178 : Prop17_8 := P2S2.prop17_8_thm h172 h171 hAB
  have h176 : Lemma17_6 := P2S2.lemma17_6_thm h171
  have h182 : Lemma18_2 := lemma18_2_thm h171 h176 hL31 hSch
  have h183 : Lemma18_3a := lemma18_3a_of_182 h182 h171 hL31
  have hMin : MinIndexL34 := minIndexL34
  have hKB : KB813 := kb813_of_model kb813Model_thm
  have hKA : IVK_8_13_lift := ivk813_of_cells hMin hInv (cells813_of kL3 kU4) hKB
  have h184 : Lemma18_4ac := lemma18_4ac_of_KA h171 hL31 h183 hKA hKA2
  have h185 : Lemma18_5R := lemma18_5R_of h171 h184
  have h186 : Lemma18_6 := lemma18_6_thm hMin hInv hKB h171 hL31 bender12_thm h183 h184 hKA
  have h181 : Prop18_1 := prop18_1_thm' bender12_thm h171 hAB h178 h183 h184 h185 h186 h1123
  have h1812 : Prop18_12 := prop18_12_of hMin hInv h171 h181 hAB h1123 hL31 hKA hKB
  exact P2S1.prop18_13_of h171 h178 h1812 bender13_thm

theorem prop18_13_thm (hcov : PSp4_oddCover) : Prop18_13 :=
  prop18_13_of_cells hcov kay_L3 kay_U4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
