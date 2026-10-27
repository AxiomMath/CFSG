module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Fi22
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthInnerExport
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.OrthInner

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Assembly.LowTwoRank

theorem lieCompsExport_conj_omega (hSL : SLFactorFacts) (hSU : SUFactorFacts)
    (hOm : OmegaFactorFacts) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {t : StatedLieTag}
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) {G : Type} [Group G]
    {n ℓ f : ℕ} (hG : StatedClassicalModel G t n ℓ f) (hpℓ : p ≠ ℓ) (a : G) (ha : a ^ p = 1) :
    LieCompsExport ℓ (MulAut.conj a) := by
  refine ⟨LieSemisimple.perfectInLayer_conj_omega ht hG hp hp2 hpℓ a ha, fun K hK => ?_⟩
  obtain ⟨X, _, _, hX, -, g, hg, hker⟩ :=
    exists_lieFactor_of_component_conj_omega hSL hSU hOm hp hp2 ht hG hpℓ a ha K hK
  exact ⟨X, inferInstance, inferInstance, hX, g, hg, hker⟩

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
