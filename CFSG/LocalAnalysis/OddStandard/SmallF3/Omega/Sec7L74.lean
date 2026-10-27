module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L74Symm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma74_of (h36 : Asc82Lemma36) (h72 : Asc82Lemma72) (hP : Asc82Tab6P)
    (hI4 : Sec74NotI4) (hC : Sec74CaseC) (hB : Sec74CaseB) : Asc82Lemma74 := by
  intro G _ _ t L S z hctx
  by_cases h1 : IsConj t (t * z)
  · exact Or.inl h1
  · refine Or.inr ?_
    intro s hs hsC hst
    by_contra hα
    obtain ⟨g, rfl⟩ := isConj_iff_inv_mul.mp hs
    have hA : Sec74Ass G t L S z g := ⟨hctx, hsC, hst, h1⟩
    have hs2 : orderOf (g⁻¹ * t * g) = 2 := hA.orderOf_s
    obtain ⟨hsN, hsnC⟩ := sec7_not_central h36 h72 hctx hs2 hsC hst
    rcases hP.classify G L hctx.isOm6P (g⁻¹ * t * g) hs2 hsN with h | h | h | h | h | h
    · exact hsnC h
    · exact hI4 G t L S z g hA h
    · exact hB G t L S z g hA h
    · exact hα h
    · exact hC G t L S z g hA (Or.inl h)
    · exact hC G t L S z g hA (Or.inr h)

end CFSG.OddStandard.SmallF3.Omega
