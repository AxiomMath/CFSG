module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Final2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IBFinal
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FMain
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FMono
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FFactD
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FFactSixSix
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FClABC
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Final
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IFact214
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IFact43
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IK6
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4L41
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4L410
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4L43
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4L46
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4L48
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4L49

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

structure Asc82Sec4Inputs5 : Prop where
  split47 : Asc82Split47
  factD : Asc82FactD
  factMono : Asc82FactMono
  factSixSix : Asc82FactSixSix

theorem aschOmega7_of_sec3_sec4_5 (h3 : Asc82Sec3Results) (h4 : Asc82Sec4Inputs5) :
    AschOmega7 := by
  have h41 : Asc82Lemma41 := asc82Lemma41_of h3.l38 h3.l311
  have h42 : Asc82Lemma42 := asc82Lemma42_of h3.l33 h41
  have h43 : Asc82Lemma43 :=
    asc82Lemma43_of h3.l36 h3.l37 h42 asc82Fact43_holds asc82Fact43Class_holds
  have hAD : Asc82ADataExists :=
    sec4_exists_AData h3.l36 h42 asc82FactE64_holds asc82FactCentB_holds
  have h44d : Asc82Lemma44d := asc82Lemma44d_of hAD
  have h44e : Asc82Lemma44e := asc82Lemma44e_of hAD
  have h46a : Asc82Lemma46a := asc82Lemma46a_of h43 h44d h44e
  have h46b : Asc82Lemma46b := asc82Lemma46b_of h43 h46a hAD
  have h47 : Asc82Lemma47 :=
    asc82Lemma47_of_frames
      { h36 := h3.l36
        h39 := h3.l39
        h42 := h42
        h43 := h43
        h46b := h46b
        hAD := hAD
        hf43c := asc82Fact43Class_holds
        hf6 := asc82Fact6Class_holds
        hf214 := asc82Fact214_holds
        hin6 := asc82FactInner6_holds
        hk6 := asc82FactK6_holds
        hcB := asc82FactCentB_holds
        hD := h4.factD
        hMono := h4.factMono
        h66 := h4.factSixSix
        hABC := asc82ClaimsABC_of h3.l36 h43 asc82Fact43Class_holds } h4.split47
  have h48a : Asc82Lemma48a := asc82Lemma48a_of h43 h47
  have h48b : Asc82Lemma48b := asc82Lemma48b_of h43 h46a h47
  have h49 : Asc82Lemma49 := asc82Lemma49_of h3.l39 hAD asc82FactK6_holds
  exact aschOmega7_of_410ctx_seven (asc82Lemma410Ctx_of h46b h47 h48a h48b h49 hAD)
    (asc82ZExists7_of h3.l36)

structure Asc82Sec4Open2 : Prop where
  split47 : Asc82Split47

theorem Asc82Sec4Open2.toInputs5 (h : Asc82Sec4Open2) : Asc82Sec4Inputs5 :=
  ⟨h.split47, asc82FactD_holds, asc82FactMono_holds, asc82FactSixSix_holds⟩

theorem aschOmega7_of_sec3_sec4_open2 (h3 : Asc82Sec3Results) (h4 : Asc82Sec4Open2) :
    AschOmega7 :=
  aschOmega7_of_sec3_sec4_5 h3 h4.toInputs5

end CFSG.OddStandard.SmallF3.Omega
