module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddL3Final
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115EvenUnitary
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddU3AutFinal
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115CoverAlt
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115SporadicJ2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.InnerCoverSporadic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.InnerCoverMain
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Alt

public section

namespace CFSG.QuasithinUnique

open CFSG.QuasithinUnique.Ch1 CFSG.Milestones

theorem lemma115_3_List_of_rest_inputs'
    (hT : K1.TitsSylowCentralizingAutInner)
    (hS : SporadicRestAutInner) (hTC : TitsTwoCoverTrivial) : Lemma115_3_List :=
  have hE := evenLieAutInner_of_tits hT
  lemma115_3_List_of_nonSporadic_inspections
    (simpleInspection_nonSporadic (simpleInspection_altList hE)
      (simpleInspection_oddList (oddAutInner_of oddDegreeThreeAutInner)
        oddInvolutionCentralizers)
      (simpleInspection_charTwoList hE))
    (fun _ _ _ _ h hz hK =>
      invCaseF_of_sporadic (sporadicAutInner_of_residual (sporadicResidualAutInner_of_rest hS)) h
        hz hK)
    (innerCover_nonSporadic hTC) altOuterCover

end CFSG.QuasithinUnique
