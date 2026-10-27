module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.OrthAux.Descent
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Split

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.ComponentClassification.CatLeaf
  CFSG.RankThree.PartOne.Sec66T

theorem noL2OuterAt_orthPlus (hO : LieOrderFormulasInput) : NoL2OuterAt FamOrthPlus := by
  intro P _ _ t n p f _ _ hF hm ψ hψ3 hninn
  obtain ⟨rfl, hn5⟩ := hF
  have hC : StatedClassicalModel P .POmegaPlus n p f :=
    (lieModel_classical_iff (by decide)).mp hm
  exact OrthAux.noL2Layer_omega_plus_outer hO hC hn5 hψ3 fun a h => hninn ⟨a, h⟩

section Final


theorem y923_orthPlus_holds : Y923_OrthPlus :=
  y923_lieRestAt_of_noL2Outer
    (noL2OuterAt_orthPlus CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput)

end Final

end CFSG.HardMathSupport.Dickson.Sec6.I923
