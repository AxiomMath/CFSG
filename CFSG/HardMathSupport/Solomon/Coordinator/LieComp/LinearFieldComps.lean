module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Fi22
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SLFacts
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearFieldExport

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.LocalAnalysis.ComponentInitial

theorem lieCompsExport_fieldAut (hSL : SLFactorFacts) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {n : ℕ} (hn : 2 ≤ n) {k : Type} [Field k] [Finite k] (σ : k ≃+* k) (hσ : orderOf σ = p) :
    LieCompsExport (ringChar k) (LinearFlag.fieldAut n k σ) := by
  refine ⟨?_, fun K hK => ?_⟩
  · rcases Nat.lt_or_ge n 3 with h | h
    · obtain rfl : n = 2 := by omega
      exact LieSemisimple.perfectInLayer_fieldAut_two σ
    · exact LieSemisimple.perfectInLayer_fieldAut h hp hp2 σ hσ
  · obtain ⟨hperf, f, hf, hfk⟩ := linearFieldAut_components hn σ K hK
    exact ⟨_, inferInstance, inferInstance, linearFieldAut_lieFactorData hSL hn σ hperf, f, hf,
      hfk⟩

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
