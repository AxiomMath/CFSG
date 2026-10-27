module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4S47RMain
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Final5

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec4FInputs_of_sec3 (h3 : Asc82Sec3Results) : Sec4FInputs := by
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
  exact
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
      hD := asc82FactD_holds
      hMono := asc82FactMono_holds
      h66 := asc82FactSixSix_holds
      hABC := asc82ClaimsABC_of h3.l36 h43 asc82Fact43Class_holds }

theorem aschOmega7_of_sec3 (h3 : Asc82Sec3Results) : AschOmega7 :=
  aschOmega7_of_sec3_sec4_open2 h3 ⟨asc82Split47_holds (sec4FInputs_of_sec3 h3)⟩

end CFSG.OddStandard.SmallF3.Omega
