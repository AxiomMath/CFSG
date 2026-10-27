module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.OrthAux.Descent
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Split

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.ComponentClassification.CatLeaf
  CFSG.RankThree.PartOne.Sec66T

theorem noL2OuterAt_orthOdd (hO : LieOrderFormulasInput) : NoL2OuterAt FamOrthOdd := by
  intro P _ _ t n p f _ _ hF hm ψ hψ3 hninn
  obtain rfl := hF
  have hC : StatedClassicalModel P .POmegaOdd n p f :=
    (lieModel_classical_iff (by decide)).mp hm
  exact OrthAux.noL2Layer_omega_odd_outer hO hC hψ3 fun a h => hninn ⟨a, h⟩

section Final


theorem y923_orthOdd_holds : Y923_OrthOdd :=
  y923_lieRestAt_of_noL2Outer
    (noL2OuterAt_orthOdd CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput)

end Final

end CFSG.HardMathSupport.Dickson.Sec6.I923
