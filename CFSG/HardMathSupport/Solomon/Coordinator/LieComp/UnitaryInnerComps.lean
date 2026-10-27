module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Fi22
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryInnerExport

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel

theorem lieCompsExport_primeFormConjHom (hSL : SLFactorFacts) (hSU : SUFactorFacts) {p : ℕ}
    (hp : p.Prime) {ℓ f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) (hpℓ : p ≠ ℓ)
    (A : primeFormUnitary h (idGram K n)) {c : Kˣ}
    (hA : (A : GL (Fin n) K) ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c) :
    LieCompsExport ℓ (primeFormConjHom h (idGram K n) A) := by
  refine ⟨LieSemisimple.perfectInLayer_primeFormConjHom h hp hpℓ A hA, fun T hT => ?_⟩
  obtain ⟨X, _, _, hX, -, g, hg, hker⟩ :=
    exists_lieFactor_of_component_primeFormConjHom hSL hSU hp hpℓ A hA T hT
  exact ⟨X, inferInstance, inferInstance, hX, g, hg, hker⟩

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
