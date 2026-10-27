module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13KMain
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbM4Fin
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13a5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13b5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13c10
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d9
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e8
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4Glue
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4SZ
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4NR
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JMain
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ACorA

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

theorem gh74Statement_of_gh74ModelsInput
    (hGH : CFSG.ComponentClassification.UFrontier.GH74ModelsInput) :
    CFSG.GH74.GH74Statement := by
  intro G _ _ hsimple hnonab hrank hgen
  letI := hsimple
  exact hGH G hnonab hrank (fun P hP => hgen P hP)

theorem sec4Inputs_of_gh74ModelsInput
    (hGH : CFSG.ComponentClassification.UFrontier.GH74ModelsInput) : Sec4Inputs :=
  ⟨gh74Statement_of_gh74ModelsInput hGH, corAStatement_of_certificates⟩

theorem harris1981_bound_of_gh74ModelsInput
    (hGH : CFSG.ComponentClassification.UFrontier.GH74ModelsInput) :
    FritzII.Harris1981Bound :=
  harris1981_bound_reduced13G
    (lemma4_11_of_ab (sec4Inputs_of_gh74ModelsInput hGH) (l411_ab_of_steps l411_zsetup_holds
        l411_zinsyl_holds l411_znotsyl_holds))
    (S4B.lemma4_13_of_families S4B.q13a_famA S4B.q13b_famB S4B.q13c_famC S4B.q13d_famD S4B.q13e_famE)
    (sec4Inputs_of_gh74ModelsInput hGH)

end CFSG.OddStandard.SmallF3.HarrisU33
