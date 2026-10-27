module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec4C8Q
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec4C8Asm
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec4C8HypFin
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Wired
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec4C8E
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec4C8Lift
public import CFSG.Quasithin.Vol2.Ch12Sec4C8A7

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

theorem charTwo1248_F4_of_inputs
    (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4) (h323 : Stmt3_2_3) (h3228 : Stmt3_2_2_eight)
    (hpre : Pre1242_F4) (h1229 : Stmt12_2_9_F4) (h68 : E6.E68Stmt) (hlist : Lemma115_3_List)
    (hF318 : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK) (hKF : KnownFacts15122Types)
    (hP3 : E6.E619Insp) (hKG1 : L32ListFact1248) (hKG2 : L33ExclusionFact)
    (hKG3 : HatA67Fact1248) (hKG4 : L2pThreeFact1248) (hKG5 : L2pEmbedFact1248)
    (hI31 : AS_I_3_1_one_two) : CharTwo1248_F4 := by
  have hinv := involFact1248_of_F4 h331 h1222 hpre (stmt12_2_10_of_1222_F4 h1222)
  have hX := hypX1248_of_g2_F4 h331 h1222 h1229 hpre
  exact charTwo1248_of_F4
    (noComp1248_of_F4 hX
      (comp1248Type_of_F4 h331 h1222 h323 h3228 hpre hinv hX h68 hlist hF318 h36 h38 hKF hKG1 hKG2
        hKG3 hKG4)
      (comp1248Lift_of_F4 h331 h1222 h323 h3228 hpre hinv h68 hlist hF318 h36 h38 hKF hKG1 hKG2
        hKG3 hI31 hKG5))
    (oddCore1248_of_F4 h331 h1222 hpre (oddInv1248_of_F4 h331 h1222 h323 h3228 hpre hinv)
      (oddCentE1248_of_F4 h331 h1222 h323 h3228 hpre hinv hlist hP3 a7Insp1248)
      (oddCentQ1248_of_F4 h331 h1222 hpre) (oddFinal1248_of_F4 h331 h1222 hpre))

end CFSG.Quasithin.H13
