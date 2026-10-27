module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Fi22
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SpFacts
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympFieldExport

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.UnbalancedCatalog (descentField)

theorem lieCompsExport_fieldAut_sp (hSp : SpFactorFacts) (hSp42 : SpFourTwoFacts) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {r : ℕ} (hr : 2 ≤ r) {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) (hσ : orderOf σ = p) :
    LieCompsExport (ringChar K) (SymplecticHigher.fieldAut r K σ) := by
  have hσp : σ ^ p = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hodd : Odd p := hp.odd_of_ne_two hp2
  refine ⟨LieSemisimple.perfectInLayer_fieldAut_sp hr hp hp2 σ hσp, fun K' hK' => ?_⟩
  by_cases hex : r = 2 ∧ Nat.card ↥(descentField σ) = 2
  · obtain ⟨rfl, hk2⟩ := hex
    obtain ⟨hLF, hcover⟩ := sp_fieldAut_comp_two hSp42 hodd σ hσp hk2
    obtain ⟨f, hf, hfk⟩ := hcover K' hK'
    exact ⟨_, inferInstance, inferInstance, hLF, f, hf, hfk⟩
  · obtain ⟨hLF, hcover⟩ := sp_fieldAut_comp_generic hSp hodd hr σ hσp hex
    obtain ⟨f, hf, hfk⟩ := hcover K' hK'
    exact ⟨_, inferInstance, inferInstance, hLF, f, hf, hfk⟩

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
