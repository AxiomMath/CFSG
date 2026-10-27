module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem14Five
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem14Mod

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3

theorem stmt6_1_14_F4 (h432 : Stmt4_3_2_F4) (h6110 : Stmt6_1_10_F4) (h37 : Vol2Native.A37ForSQTKCat)
    (h39 : Vol2Native.A39ForSQTKCat) : Stmt6_1_14_F4 := by
  intro G _ _ T M L V n h hev t htT ht U hU hSyl
  subst hU
  exact ⟨h.lemma_6_1_14_one_F4 h432 htT ht hSyl, h.lemma_6_1_14_two htT,
    h.lemma_6_1_14_three_F4 h6110 htT ht, h.lemma_6_1_14_four_F4 h432 h6110 htT ht hSyl,
    fun hn g hA hVA hne => h.lemma_6_1_14_five_F4 h432 h6110 h37 h39 hev htT ht hSyl hn g hA hVA hne⟩

end CFSG.Quasithin.H13
