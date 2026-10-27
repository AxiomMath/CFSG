module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Main
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L73
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L74
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L74I4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L74C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L74BX
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L74B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L75
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L76
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L76C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec710A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec710C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec710D
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7End
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.S7FU
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.S7FPrince
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.S7FY

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem s7f_aschOmega6Plus_of_inputs (hZ : Asc82ZExists) (hsh : Asc82Shapes)
    (h33 : Asc82Lemma33) (h35 : Asc82Lemma35) (h36 : Asc82Lemma36) (h37 : Asc82Lemma37)
    (hP : Asc82Tab6P) (hM : Asc82Tab6M) (hP7 : Asc82Tab7P) (hF : Asc82AutFacts)
    (hO : Asc82Outside) (hF5 : Asc82Fink5) (h77b : Asc82Lemma77b) (h78 : Asc82Lemma78)
    (h63 : Asc82Lemma63) (hAb : Asc82AbelAutBound) : AschOmega6Plus := by
  intro G _ _ t L hS hL
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hSyl⟩ : ∃ S : Subgroup G, IsSylow2Of S (centralizer ({t} : Set G)) :=
    ⟨_, isSylow2Of_map_sylow (Classical.arbitrary (Sylow 2 ↥(centralizer ({t} : Set G))))⟩
  obtain ⟨z, hz⟩ := hZ G t L hS S hSyl
  have hctx : Sec7Ctx G t L S z := { toSec3SettingLB := hS, toAsc82Notation := hz, omega6 := hL }
  have h71 := asc82Lemma71_of hsh
  have h72 := asc82Lemma72_of h33 h71
  have h73 := asc82Lemma73_of h36 h37 hP
  have hBX := sec74BX_of h36 h72 h73 hP hF hO
  have h74 := asc82Lemma74_of h36 h72 hP (sec74NotI4_of h36 h72 h73 hP hF)
    (sec74CaseC_of h36 h72 h73 hP hF hO)
    (sec74CaseB_of h36 h72 h73 hP hF hBX (sec74BT_of h36 h72 hP hBX))
  have h75a := asc82Lemma75a_of h36 hP
  have h75b := asc82Lemma75b_of h36 hP
  have h76 := asc82Lemma76_of h36 h72 h73 h74 hP hO hF5
  have h76c := asc82Lemma76Choice_of h36 h74 hP h75a h75b
  have h79a := asc82Lemma79a_of h36 h72 h76 hP hP7 h77b h78
  have h710a := asc82Lemma710a_of h36 hP h79a
  have h710b := asc82Lemma710b_of h36 h72 h73 hP hF h79a h710a
  have h710c := asc82Lemma710c_of h36 hP h75b h78 h710b
  have h710d := asc82Lemma710d_of h36 hP hF hP7 h77b h78 h710b h710c
  have hE := asc82Final7E_of_sec7 h36 h76 hP h77b h78 h710c h710d
  have hPr := asc82Final7Prince_of_sec7 h36 h76 hP h77b h78 h710c h710d
  have hY := asc82Final7Y_of_sec7 h33 h35 h36 h63 h78 hsh hP hM hF hZ h76c h79a
  obtain ⟨g, B, hc⟩ := h76c G t L S z hctx
  exact sec711_false h36 h35 h75b hP hM hF hP7 hE hPr hY hAb hc

end CFSG.OddStandard.SmallF3.Omega
