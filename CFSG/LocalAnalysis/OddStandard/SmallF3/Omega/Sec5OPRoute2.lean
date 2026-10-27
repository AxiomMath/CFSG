module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OPDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OP6Main
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qP510Orb
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3q510

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Pocket510_of_route2 (hy : Sec5B59Hyp) (h52a : Asc82Lemma52a) (h58d : Asc82Lemma58d)
    (hD : Asc82FactQCentOrd6) (hB : Asc82FactBCent6) (h4 : Asc82FactReflCentQ6)
    (hF0 : Asc82FactPockets6) (hTE : Asc82P510TE) (hTR : Asc82P510TR) : Asc82Pocket510 := by
  intro G _ _ t L S z r B A hR h7 hnc
  obtain ⟨ρ, φ, h⟩ := sec5p510_ctx_of hy h58d hR h7 hnc
  obtain ⟨K₁, K₂, a, b, hs⟩ := sec5p510_stage1 hy h52a hD hB h4 hF0 h
  have hK : ∃ K : Subgroup G, Sl23PocketIn L z K ∧
      ⁅K, sec5op_Y t z⁆ ≤ oddCoreIn (sec5op_Y t z) := by
    rcases hs.T_cases with hT | hT
    · exact hTE G t L S z r ρ B A φ K₁ K₂ a b h hs hT
    · exact hTR G t L S z r ρ B A φ K₁ K₂ a b h hs hT
  obtain ⟨K, hKp, hKY⟩ := hK
  have hSec5 : Sec5Ctx G t L S z := h.toSec5Ctx
  have htH : t ∈ centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hSec5.central t (sec5p510_t_mem_S hSec5)
  refine ⟨K ⊔ oddCoreIn (centralizer ({z} : Set G)), ?_⟩
  exact sec5op6_pocket_of_L hSec5.involution (sec5p510_L_le_centralizer_t hSec5)
    (fun c hc => conjugate_eq_self_of_lemma36 hy.h36 hSec5.toSec5Setting.toSec3SettingLB c hc)
    hKp (sec5op_Y_le htH) (sec5op_Y_normal t z) (sec5op_t_mem_Y t z) hKY

end CFSG.OddStandard.SmallF3.Omega
