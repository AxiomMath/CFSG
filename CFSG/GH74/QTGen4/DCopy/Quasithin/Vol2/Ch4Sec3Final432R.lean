module

public import CFSG.Quasithin.Vol2.Ch4Sec3L4316Cfg
public import CFSG.Quasithin.Vol2.Ch4Sec3C135Holds
public import CFSG.Quasithin.Vol2.KGFactKGU35
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE22NoNProved
public import CFSG.Quasithin.Vol2.Ch3xC58NSMPB
public import CFSG.Quasithin.Vol2.Ch4Sec3L436Sp4Mult
public import CFSG.Quasithin.Background.A318PFacts2
public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremEB51
public import CFSG.Quasithin.Vol2.Ch11SecB414Z
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4Holds
public import CFSG.Quasithin.Vol2.KGFactInsp4316
public import CFSG.Quasithin.Vol2.KGFactInspOutDer
public import CFSG.Quasithin.Vol2.KGFactInspE16m
public import CFSG.Quasithin.Vol2.KGFactInspE16L
public import CFSG.Quasithin.Vol2.KGFactInspExc
public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspG2
public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspD4
public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspF4
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch4Sec3L4316
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch4Sec3L43Q517
import CFSG.Quasithin.Vol2.Ch4Sec3Sp4Gen
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeLocalNormal
public import CFSG.Quasithin.H13.VolIA36
public import CFSG.Quasithin.Vol2.Ch4Sec3C136
public import CFSG.Quasithin.Vol2.Ch4Sec3C53
public import CFSG.Quasithin.Vol2.Ch4Sec3C64
public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspFFG2BT
public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspRed

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem stmt4_3_2_of_rest_F4
    (hC48 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC48Statement G) (hM2223 : Insp436M22M23)
    (h134 : MS93.AS_C_1_34_corr_F4) (hZ : Gap437Sp4Z) : Stmt4_3_2_F4 := by
  have hR : L2RankOneSylowFact := NQCat.l2RankOneSylowFact_holds
  have hMult : Sp4MultTrivial :=
    sp4MultTrivial_of CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  have hF : A318Facts := a318Facts_of_two qSporOutTwo_holds R3c18.qLiePRank_holds
  have hB414 : LemmaB414Corrected := B414.lemmaB414Corrected_holds
  have h135 : AsC135Three := asC135Three_holds
  have hC : LemmaC53C56Six := lemmaC53C56Six_of theoremC126_proved C58NS.minParabolicBlockSubnormal_holds
  have h36 : A36ForSQTK := CFSG.Quasithin.H13.VolI.a36ForSQTK_holds
  have h37 : A37ForSQTK := a37ForSQTK_of_cat Vol2Native.a37ForSQTKCat_proved
  have h38 : A38ForSQTK := a38ForSQTK_of_cat
    (Vol2Native.a38ForSQTKCat_of_facts CFSG.Quasithin.mult2Fact Vol2Native.a134SQTKFactCat
      Vol2Native.a36CoreForSQTKCat_proved Vol2Native.a37ForSQTKCat_proved)
  have h39 : A39ForSQTK := a39ForSQTK_of_cat Vol2Native.a39ForSQTKCat_proved
  have h122 : Lemma122A := fun G _ _ hS hQ hna H L hH hL p hp hp2 hc hd =>
    Vol2Native.lemma122A_proved G hS hna (qtkeCore_of_cat hna hQ) H L hH hL p hp hp2 hc hd
  have hUpto : Lemma43Upto_F4 := lemma43Upto_of_F4 h135 hR hC h36 h37 h38 h39
    (A38c14.a312ForSQTK_of_residual A3Facts.a134ForSQTK A3Facts.schreierSQTK
      A38c17.a312ResidualRest2_holds.toRest3.toRest4.toRest10.toRest) h134 h122 hF
    (KGInsp4316.insp4316_of KGInsp4316.insp4316OutDer_holds KGInsp4316.insp4316E16m_holds
      KGInsp4316.insp4316E16L_holds
      (KGInsp4316.insp4316L3eps_of KGInsp4316.insp4316L3epsOdd_holds)
      (KGInsp4316.insp4316OutLie_of KGInsp4316.insp4316OutLieOdd_holds
        (KGInsp4316.insp4316OutLieRank2_of KGInsp4316.insp4316OutLieExc_holds)))
    (step43L34_of hB414 h135 hR hC h36 h37 h38 h39)
    (step43U35_of KGU35.kgu35_holds h135 hR hC h36 h37 h38 h39)
  have hInsp : Insp436Sp4 := insp436Sp4_of insp436G2_holds insp436D4_holds insp436F4_holds hM2223
  have hFF : InspFF436 := inspFF436_holds
  have hStep : Step436Sp4 :=
    step436Sp4_of h36 h37 h38 h122 hF asB56_holds hFF (step436KZ_holds h37 h39)
  exact stmt4_3_2_of_F4 hR hC (core432_of_F4 hR hC hC48 inspC48L2_holds h36 h37 h38 h39
    (lemma436Comp_of hR hC h36 h37 h38 h39 hInsp
      (lemma436Sp4_of h37 h38 h39 hMult sp4ParabolicFacts_holds hStep))
    (lemma437Sp4_holds hR hC h37 h38 h39 (gap437Sp4Z_of hR hC h37 h38 h39))
    (lemma437A7_holds hR hC h37 h38 h39 lemmaC64Ten_holds)
    (lemma437SL3_holds hR hC h37 h38 h39 sl3ParabolicAutFact_holds)
    (lemma439_of (lemma439Fix_holds hR hC h37 h38 h39 sl3ParabolicAutFact_holds))
    (lemma4310_of (lemma4310Two_holds hR hC h37 h38 h39 sl3ParabolicAutFact_holds lemmaC136_holds)
      hR hC h37 h38 h39)
    (lemma43End_of_b414_F4 hUpto hB414))

end CFSG.Quasithin.H13.Ch4
