module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Statements2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L126A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L126B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L126D
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L126F

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma126_of (hp : Asc82Pre11) (h120 : Asc82Lemma120) (h121 : Asc82Lemma121)
    (h122 : Asc82Lemma122) (h123 : Asc82Lemma123) (h124 : Asc82Lemma124) : Asc82Lemma126 := by
  intro G _ _ t L S z K1 K2 E hctx h hh
  obtain ⟨hV8, hBV, hVE, hEN, hVsup, hVinf, hVC⟩ := sec126_V_facts hp h120 h121 h124 hctx
  obtain ⟨hAS, hBe, hA5⟩ := sec126_isElemAb2_secA hp hctx.toSec10Z
  obtain ⟨hBL, hB16, -, -, -, -, -, -⟩ := sec10BData_of hp.basic hp.facts.b5 hctx.toSec10Z
  obtain ⟨hA1, -⟩ := hctx.alt1
  have hJ := sec126_A_eq_jElem hp h122 h123 hctx
  have hrank := sec126_rank_ct hctx.sylow hA5 hAS hJ
  have ht2 : t * t = 1 := sec126_mul_self_of_orderOf hctx.involution
  have ht1 : t ≠ 1 := by
    intro h1
    have := hctx.involution
    rw [h1, orderOf_one] at this
    omega
  have hVt : ∀ g : G, g⁻¹ * t * g ∉ secV t S L E :=
    sec126_not_conj_mem hV8.1 (by rw [hV8.2]; norm_num) (fun F hF hFe => (hrank F hF hFe).1)
  have htA : t ∈ secA t S L := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  obtain ⟨c, hcC, hDeq, hFA, hconj⟩ :=
    sec126_D_data ht2 ht1 hB16 hV8.1 hV8.2 hVt hrank hA1 hh
  exact ⟨⟨c, hcC, hDeq⟩, sec126_fusion_N ht2 hB16 hV8.1 hV8.2 htA hA1 hctx.sylowE hVsup hEN hVC
    hh hDeq hFA hconj⟩

end CFSG.OddStandard.SmallF3.Omega
