module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OrtHFam
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.Char3Fam
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.OrthOdd
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.OrthPlus
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.OrthMinus

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Dickson.Sec6.I923

theorem y1431_noCfg_orthOdd (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (hKD : KDCharP 3) : Y1431NoCfgAt FamOrthOdd := by
  refine Y1431NoCfgAt.of_cover
    (Fam₁ := fun t n p f => FamOrthOdd t n p f ∧ p ≠ 3)
    (Fam₂ := fun t n p f => FamOrthOdd t n p f ∧ p = 3)
    (fun t n p f hF => ?_) (y1431_noCfg_orthOddNe3' hO)
    (y1431NoCfgAt_char3_of_bridges hKD (Or.inl ?_) (fun t n p f hF => hF.2)
      (hOK_of_noL2OuterAt (noL2OuterAt_mono (fun t n p f hF => hF.1) (noL2OuterAt_orthOdd hO))))
  · by_cases hp : p = 3
    · exact Or.inr ⟨hF, hp⟩
    · exact Or.inl ⟨hF, hp⟩
  · rintro t n p f ⟨rfl, -⟩
    simp [CFSG.Blueprint.classicalTags]

theorem y1431_noCfg_orthPlus (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (hKD : KDCharP 3) : Y1431NoCfgAt FamOrthPlus := by
  refine Y1431NoCfgAt.of_cover
    (Fam₁ := fun t n p f => FamOrthPlus t n p f ∧ p ≠ 3)
    (Fam₂ := fun t n p f => FamOrthPlus t n p f ∧ p = 3)
    (fun t n p f hF => ?_) (y1431_noCfg_orthPlusNe3' hO)
    (y1431NoCfgAt_char3_of_bridges hKD (Or.inl ?_) (fun t n p f hF => hF.2)
      (hOK_of_noL2OuterAt (noL2OuterAt_mono (fun t n p f hF => hF.1) (noL2OuterAt_orthPlus hO))))
  · by_cases hp : p = 3
    · exact Or.inr ⟨hF, hp⟩
    · exact Or.inl ⟨hF, hp⟩
  · rintro t n p f ⟨⟨rfl, -⟩, -⟩
    simp [CFSG.Blueprint.classicalTags]

theorem y1431_noCfg_orthMinus (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (hKD : KDCharP 3) : Y1431NoCfgAt FamOrthMinus := by
  refine Y1431NoCfgAt.of_cover
    (Fam₁ := fun t n p f => FamOrthMinus t n p f ∧ p ≠ 3)
    (Fam₂ := fun t n p f => FamOrthMinus t n p f ∧ p = 3)
    (fun t n p f hF => ?_) (y1431_noCfg_orthMinusNe3' hO)
    (y1431NoCfgAt_char3_of_bridges hKD (Or.inl ?_) (fun t n p f hF => hF.2)
      (hOK_of_noL2OuterAt (noL2OuterAt_mono (fun t n p f hF => hF.1) (noL2OuterAt_orthMinus hO))))
  · by_cases hp : p = 3
    · exact Or.inr ⟨hF, hp⟩
    · exact Or.inl ⟨hF, hp⟩
  · rintro t n p f ⟨rfl, -⟩
    simp [CFSG.Blueprint.classicalTags]

end CFSG.HardMathSupport.Dickson.Sec6.I1431
