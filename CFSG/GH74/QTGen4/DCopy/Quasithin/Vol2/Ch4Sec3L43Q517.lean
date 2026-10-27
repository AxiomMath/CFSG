module

public import CFSG.Quasithin.Vol2.Ch4Sec3L43Q517
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch4Sec3L43L34

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank
open scoped Pointwise

variable {G : Type} [Group G]

theorem lemma43End_of_jh_F4 (hUpto : Lemma43Upto_F4) (hB414 : LemmaB414Corrected)
    (hJH : OperatorJHNatEig) : Lemma43End_F4 :=
  lemma43End_of_F4 hUpto hB414 (gap432L34Twisted_holds hJH hB414)

theorem lemma43End_of_b414_F4 (hUpto : Lemma43Upto_F4) (hB414 : LemmaB414Corrected) : Lemma43End_F4 :=
  lemma43End_of_jh_F4 hUpto hB414 OperatorJH.operatorJHNatEig_holds

end CFSG.Quasithin.H13.Ch4
