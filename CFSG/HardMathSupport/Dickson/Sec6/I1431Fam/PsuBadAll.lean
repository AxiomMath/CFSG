module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PsuBFam
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PsuBadHigh

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank

theorem y1431_noCfg_psuBad (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (hGA : GriessAllModelsStatement) : Y1431NoCfgAt FamPsuBadRest := by
  refine Y1431NoCfgAt.of_cover (Fam₁ := FamPsuBadThree) (Fam₂ := FamPsuBadHigh)
    (fun t n p f hF => ?_) (y1431_noCfg_psuBadThree hO) (y1431_noCfg_psuBadHigh hGA)
  obtain ⟨ht, hn3, hdiv, hn6'⟩ := hF
  have h3n : 3 ∣ n := (Nat.dvd_gcd_iff.1 hdiv).1
  by_cases hn6 : 6 ≤ n
  · exact Or.inr ⟨⟨ht, hn3, hdiv, hn6'⟩, hn6⟩
  · refine Or.inl ⟨⟨ht, hn3, hdiv, hn6'⟩, ?_⟩
    obtain ⟨k, rfl⟩ := h3n
    omega

end CFSG.HardMathSupport.Dickson.Sec6.I1431
