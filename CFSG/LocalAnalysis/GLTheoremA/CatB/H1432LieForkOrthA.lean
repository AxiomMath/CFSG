module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432LieForkDefs
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Split
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432LieForkBase
import CFSG.LocalAnalysis.GLTheoremA.CatA.H1429SubOrth

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.HardMathSupport.Dickson.Sec6.I923 (FamOrthOdd FamOrthPlus FamOrthMinus)
open CFSG.LocalAnalysis.GLTheoremA.H1429Sub (exists_fixModel_pomegaOdd
  exists_fixModel_pomegaPlus exists_fixModel_pomegaMinus)

theorem lieOuterThreeAt_orthOdd : LieOuterThreeAt FamOrthOdd := by
  intro P _ _ t n f _ hF hm ψ hψ3 hψ A hA
  obtain rfl := hF
  obtain ⟨a, -, hf, hmA⟩ :=
    exists_fixModel_pomegaOdd (hm.statedClassicalModel (by decide)) hψ3 hψ hA
  exact outerLayerThree_of_field (by decide) hf.symm (Or.inl ⟨by decide, hmA⟩)

theorem lieOuterThreeAt_orthPlus : LieOuterThreeAt FamOrthPlus := by
  intro P _ _ t n f _ hF hm ψ hψ3 hψ A hA
  obtain ⟨rfl, hn5⟩ := hF
  obtain ⟨a, -, hf, hmA⟩ :=
    exists_fixModel_pomegaPlus hn5 (hm.statedClassicalModel (by decide)) hψ3 hψ hA
  exact outerLayerThree_of_field (by decide) hf.symm (Or.inl ⟨by decide, hmA⟩)

theorem lieOuterThreeAt_orthMinus : LieOuterThreeAt FamOrthMinus := by
  intro P _ _ t n f _ hF hm ψ hψ3 hψ A hA
  obtain rfl := hF
  obtain ⟨a, -, hf, hmA⟩ :=
    exists_fixModel_pomegaMinus (hm.statedClassicalModel (by decide)) hψ3 hψ hA
  exact outerLayerThree_of_field (by decide) hf.symm (Or.inl ⟨by decide, hmA⟩)

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
