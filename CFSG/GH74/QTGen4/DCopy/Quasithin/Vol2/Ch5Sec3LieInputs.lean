module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec3L3ExcMain
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec3L3F533
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec3Lemma531
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.GoldschmidtSec53FactsLie
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.GoldschmidtSec53FactsSp

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

theorem stmt5_3_2At_of_F4 (h532 : Stmt5_3_2_F4) (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m : ℕ) :
    Stmt5_3_2At_F4 t m :=
  fun G _ _ T M L V H B D L₂ n f hyp hty hpar => h532 G T M L V H B D L₂ n t m f hyp hty hpar

theorem stmt5_3_Lie_of_inputs_F4
    (h39 : Vol2Native.A39ForSQTKCat) (hC58 : TheoremC58) (h511 : Stmt5_1_1_F4) (h527 : Stmt5_2_7_F4)
    (h532 : Stmt5_3_2_F4) (h431 : F431Rank2)
    (hG2 : Sec53F.LieFactsAt .G2 0) (h3D4 : Sec53F.LieFactsAt .trialityD4 0)
    (h2F4 : Sec53F.LieFactsAt .twistedF4 0) (hU4 : Sec53F.LieFactsAt .PSU 4)
    (hU5 : Sec53F.LieFactsAt .PSU 5) : Stmt5_3_Lie_F4 := by
  have h531 := stmt5_3_1_of_F4 h39 hC58 h511 h527
  have h537 := stmt5_3_7_of_F4 h531 (stmt5_3_L3_facts_of_F4 h527 h531)
    (Sec53L3.stmt5_3_7_exc_of_F4 h527 h531)
  have hfacts := Sec53L3.stmt5_3_3_facts_of_F4 h527 h531
    (Sec53F.stmt5_3_3_factsAt_PSp_F4 h527 h531 (stmt5_3_2At_of_F4 h532 _ _))
    (Sec53F.stmt5_3_3_factsAt_of_lieFacts_F4 (by decide) hG2 h527 h531 (stmt5_3_2At_of_F4 h532 _ _))
    (Sec53F.stmt5_3_3_factsAt_of_lieFacts_F4 (by decide) h3D4 h527 h531 (stmt5_3_2At_of_F4 h532 _ _))
    (Sec53F.stmt5_3_3_factsAt_of_lieFacts_F4 (by decide) h2F4 h527 h531 (stmt5_3_2At_of_F4 h532 _ _))
    (Sec53F.stmt5_3_3_factsAt_of_lieFacts_F4 (by decide) hU4 h527 h531 (stmt5_3_2At_of_F4 h532 _ _))
    (Sec53F.stmt5_3_3_factsAt_of_lieFacts_F4 (by decide) hU5 h527 h531 (stmt5_3_2At_of_F4 h532 _ _))
  exact stmt5_3_Lie_of_F4 (stmt5_3_4_of_F4 (stmt5_3_3_of_F4 h531 h532 hfacts) h431) h537

end CFSG.Quasithin.H13
