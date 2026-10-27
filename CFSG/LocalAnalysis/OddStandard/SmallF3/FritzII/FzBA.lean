module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBH3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBK2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBK3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBQ2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBTr
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBV2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBV3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzY9

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

theorem fzb_of_struct
    (hStr : FzbStructProp) : FzCaseIIr2 := by
  intro G _ _ _ t L S x₁ x₂ lam rho tau hno hAss h hK
  obtain ⟨T₂, P, q, s, hS⟩ := hStr G t L S x₁ x₂ lam rho tau hno hAss h hK
  obtain ⟨c, β, hβ, hsq⟩ := fzb_classify h hK hS
  have hI : FzbFactsI := fzb_facts_I
  have hII : FzbFactsII := fzb_facts_II
  have hF : FzbFacts c := by
    cases c
    · exact hII.1
    · exact hI.1
  have hH : c = true → FzbH1 := by
    rintro rfl
    exact hI.2
  have hV : c = false → FzbV1 := by
    rintro rfl
    exact hII.2
  obtain ⟨hq2, hq4, -, -, -⟩ := fzb_chart_q hβ hF.toFzbFactsGen
  obtain ⟨M, hMT, hMidx, hMβ⟩ := fzb_exists_M hβ hF.toFzbFactsGen hS.card_T₂
  have hqT : q ∈ T₂ := hβ.q_eq ▸ hβ.mem 64 (by norm_num)
  have hqM : q ∉ M := by
    intro hqM
    have h64 := (hMβ 64 (by norm_num)).mp (by rw [hβ.q_eq]; exact hqM)
    simp [fzbIsM] at h64
  rcases fzb_power_transfer (fzb_nonab h) (fzb_sylow_T2 hS hno) hMT hMidx hqT hqM hq4 with
    ⟨a, ha⟩ | ⟨a, ha, ha'⟩
  · exact fzb_branchA h hK hS hβ hF hH hV hMT hMβ ha
  · rw [hq2] at ha ha'
    obtain ⟨d, -, hd⟩ := fzb_qs_conj_qsy h hK hS.q_gen hS.s_cases hsq
    exact fzb_count_A6 h hK hS hβ hF (fzb_u_conj_t hβ hF.toFzbFactsGen hMβ ha ha' ⟨d, hd⟩)

end CFSG.OddStandard.SmallF3.FritzII
