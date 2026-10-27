module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Fi22
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryFieldExport

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem lieCompsExport_primeFormFieldHom (hSU : SUFactorFacts) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {ℓ f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    (hC : IsPrimeFormGram (1 : GL (Fin n) K)) (σ : K ≃+* K) (hσ : orderOf σ = p) :
    LieCompsExport ℓ (primeFormFieldHom h hC σ) := by
  haveI := h.finite
  refine ⟨LieSemisimple.perfectInLayer_primeFormFieldHom h hn hp hp2 σ hσ, fun K' hK' => ?_⟩
  obtain ⟨hne, g, hg, hgk⟩ := unitary_fieldAut_components h hn hC hp hp2 hσ K' hK'
  exact ⟨_, inferInstance, inferInstance,
    unitary_fixSubfield_lieFactorData hSU h hn hp hp2 hσ hne, g, hg, hgk⟩

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
