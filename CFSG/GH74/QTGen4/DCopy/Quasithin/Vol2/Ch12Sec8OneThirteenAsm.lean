module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneLemma8Five
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneThirteen
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneThirteen3b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneThirteenFour

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

theorem lemma12_8_13_of_F4 (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) (h1228 : Stmt12_2_8_F4)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hOut : OutFact1295) :
    Lemma12_8_13_F4 := by
  intro G _ _ T L V n V₁ V₂ hs g hg hgN
  refine ⟨L128P.thirteen_one_F4 h1222 hs hg, L128P.thirteen_two_F4 h1222 hs hg, fun hZ => ?_,
    L128P.thirteen_eight_F4 h1222 h12213 hs⟩
  rcases hs.hyp.n_mem with hn | hn | hn
  · exact L128P.thirteen_four_three_F4 h1222 h12213 h37 h38 h39 hs hn hg hgN hZ
  · exact L128P.thirteen_four_F4 h1222 h12213 h1228 h37 h38 h39
      (lemma12_8_8_five_of_F4 h1222 h12213 h37 h38 h39 hOut) hs (by omega) hg hgN hZ
  · exact L128P.thirteen_four_F4 h1222 h12213 h1228 h37 h38 h39
      (lemma12_8_8_five_of_F4 h1222 h12213 h37 h38 h39 hOut) hs (by omega) hg hgN hZ

end CFSG.Quasithin.H13
