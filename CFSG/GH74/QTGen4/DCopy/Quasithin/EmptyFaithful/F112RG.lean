module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.F112F53Res
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.F112RD
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.F112RE
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152XD

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem input15208F112Rest_of_models_F4 (hGoldP : F6.GoldschmidtCharTwoLargePair.{0})
    (hHay : HayashiFiveThree) (hTits : TitsRankLeFive) (hF4 : TwistedF4RankLeFive)
    (hR : Input15208F53Res) (h1515 : StageLemma1515CE) (h1519 : StageLemma1519)
    (h15207 : StageLemma15207_F4) (h15201 : StageLemma15201_F4) (h15112 : StageLemma15112) :
    Input15208F112Rest_F4 :=
  ⟨input15208F112At_S3_S3_of_gold_F4 hGoldP h1515 h1519 h15207 h15201 h15112,
    (input15208F112At_S3_five_of_hay_F4 hHay hTits hF4 h1515 h1519 h15207 h15201 h15112).1,
    (input15208F112At_S3_five_of_hay_F4 hHay hTits hF4 h1515 h1519 h15207 h15201 h15112).2,
    input15208F112At_S5_S3_of_res_F4 hR h1515 h1519 h15207 h15201 h15112⟩

end CFSG.Quasithin
