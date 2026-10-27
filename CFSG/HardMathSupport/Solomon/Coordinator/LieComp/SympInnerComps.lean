module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Fi22
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial

theorem lieCompsExport_conj_sp (hSL : SLFactorFacts) (hSU : SUFactorFacts) (hSp : SpFactorFacts)
    (hSp42 : SpFourTwoFacts) {p r ℓ f : ℕ} {K : Type} [Field K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hr : 1 ≤ r) (hpℓ : p ≠ ℓ)
    (x : StatedSp r K) (hx : x ^ p = 1) :
    LieCompsExport ℓ (MulAut.conj (SymplecticFlag.proj r K x)) := by
  obtain ⟨hlayer, hcomps⟩ := lieCompsCore_conj_sp (a6 := False) hSL hSU hSp hSp42 False.elim
    False.elim False.elim hp hp2 hℓ hf hK hr hpℓ False.elim x hx
  refine ⟨hlayer, fun K' hK' => ?_⟩
  obtain ⟨X, _, _, hX, hf', -⟩ := hcomps K' hK'
  exact ⟨X, inferInstance, inferInstance, hX, hf'⟩

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
