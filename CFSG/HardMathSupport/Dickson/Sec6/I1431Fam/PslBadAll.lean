module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslBadFam
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslBadHigh

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.HardMathSupport.Dickson.Sec6.I923

theorem y1431_noCfg_pslBad (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (hGA : GriessAllModelsStatement) : Y1431NoCfgAt FamPslBad := by
  refine Y1431NoCfgAt.of_cover (Fam₁ := FamPslBadThree) (Fam₂ := FamPslBadHigh)
    (fun t n p f hF => ?_) (y1431_noCfg_pslBadThree hO) (y1431_noCfg_pslBadHigh hGA)
  obtain ⟨ht, hn3, hnc⟩ := hF
  have h3n : 3 ∣ n := by
    by_contra h
    exact hnc ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
      (fun h3 => h (h3.trans (Nat.gcd_dvd_left _ _))))
  by_cases hn6 : 6 ≤ n
  · exact Or.inr ⟨⟨ht, hn3, hnc⟩, hn6⟩
  · refine Or.inl ⟨⟨ht, hn3, hnc⟩, ?_⟩
    obtain ⟨k, rfl⟩ := h3n
    omega

end CFSG.HardMathSupport.Dickson.Sec6.I1431
