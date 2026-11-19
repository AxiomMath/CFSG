module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L76A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L76B

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma76_of (h36 : Asc82Lemma36) (h72 : Asc82Lemma72) (h73 : Asc82Lemma73)
    (h74 : Asc82Lemma74) (hP : Asc82Tab6P) (hO : Asc82Outside) (hF5 : Asc82Fink5) :
    Asc82Lemma76 := by
  intro G _ _ t L S z hctx
  refine le_antisymm (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr
    ⟨hctx.t_mem_S, hctx.t_mem_centralizer⟩)) ?_
  by_contra hcon
  have h4 : ¬ ∀ x ∈ S ⊓ centralizer (L : Set G), orderOf x ≠ 4 :=
    fun h => hcon (sec76_le_zpowers_t h72 hctx h)
  push Not at h4
  obtain ⟨x, hx, hx4⟩ := h4
  by_cases hc : IsConj t (t * z)
  · exact sec76_caseA h36 h72 h73 hP hctx hc hx hx4
  · exact sec76_caseB h36 h72 h74 hP hO hF5 hctx hc hx hx4

end CFSG.OddStandard.SmallF3.Omega
