module

public import CFSG.GH74.Generic.S1.NbrCompQ3

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup CFSG.GH74.Generic

theorem s1LeafCompHigh_of_nbrComp (hN : B_S1_nbrCompHigh) (hBar : S1LeafCompBarHigh) : S1LeafCompHigh := by
  intro G _ _ x K hset hfront hbigK u hu hf hsym c hcJ hc2 hcc
  exact hN G x K hset hset.jmax hset.nothin hfront hbigK u hu hf hsym c hcJ hc2 hcc
    (hBar G x K hset hfront hbigK u hu hf hsym c hcJ hc2 hcc)

theorem s1LeafComp3_of_nbrComp (hN : B_S1_nbrComp3) (hBar : S1LeafCompBar3) : S1LeafComp3 := by
  intro G _ _ x K hset hfront u hu hf F hFld hFin hF3 hlin hodd c hcJ hc2 hcc
  exact hN G x K hset hset.jmax hset.nothin hfront u hu hf F hFld hFin hF3 hlin hodd c hcJ hc2 hcc
    (hBar G x K hset hfront u hu hf F hFld hFin hF3 hlin hodd c hcJ hc2 hcc)

theorem s1NbhdQ3Bad_of_nbrComp (hN : B_S1_nbrQ3) (hExact : S1LiftExactProp) (hK : KL3Table) :
    S1NbhdQ3Bad := by
  intro G _ _ x K hset hfront u hu hf F hFld hFin hF3 hlin hbad
  exact s1NbhdQ3BadMax_of_nbr hN hExact hK G x K hset hset.jmax hset.nothin hfront u hu hf F hFld hFin
    hF3 hlin hbad

theorem s1_shapeCase_final_nbr
    (hFrame : S1FrameExists)
    (hGriess : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hCentral : S1LiftCentralProp) (hN : B_S1_nbrComp) (hBar : S1LeafCompBar) (hK : KL3Table) :
    S_shapeCaseMaxNT @ShapeS1 :=
  s1_shapeCase_final_comp2 hFrame hGriess hCentral
    (s1CompNormal_of_leafComp (s1LiftExact_of_central_schur hCentral (s1SchurOdd_of_griess hGriess))
      (s1LeafCompHigh_of_nbrComp hN.1 hBar.1))
    (s1CompNormal3_of_leafComp (s1LeafComp3_of_nbrComp hN.2.1 hBar.2))
    (s1NbhdQ3Bad_of_nbrComp hN.2.2 (s1LiftExact_of_central_schur hCentral (s1SchurOdd_of_griess hGriess)) hK)

end CFSG.GH74.Generic.S1
