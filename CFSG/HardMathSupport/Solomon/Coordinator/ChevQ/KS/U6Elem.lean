module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.U6ElemAux
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.U6Model

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

variable {K0 : Type} [Field K0]

theorem exists_good_of_card_ge_27 [Fintype K0]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 3 K0)
    (E : Subgroup (CFSG.Open.StatedProj (CFSG.Open.StatedSU 6 (2 ^ 3) K0)))
    (hE : CFSG.Open.IsElemAbelian 3 E) (h27 : 27 ≤ Nat.card E) :
    (∃ g : CFSG.Open.StatedSU 6 (2 ^ 3) K0,
        CFSG.ComponentClassification.Burgoyne.Proj.projH _ g ∈ E ∧
        CFSG.ComponentClassification.Burgoyne.Proj.projH _ g ≠ 1 ∧
        4 ≤ maxEig (g : GL (Fin 6) K0)) ∨
    (∃ g₁ g₂ g₃ : CFSG.Open.StatedSU 6 (2 ^ 3) K0,
        CFSG.ComponentClassification.Burgoyne.Proj.projH _ g₁ ∈ E ∧
        CFSG.ComponentClassification.Burgoyne.Proj.projH _ g₂ ∈ E ∧
        CFSG.ComponentClassification.Burgoyne.Proj.projH _ g₃ ∈ E ∧
        CFSG.ComponentClassification.Burgoyne.Proj.projH _ g₃ ≠ 1 ∧
        HeisData (g₁ : GL (Fin 6) K0) g₂ g₃) := by
  by_cases hc : ∀ g₁ g₂ : CFSG.Open.StatedSU 6 (2 ^ 3) K0,
      CFSG.ComponentClassification.Burgoyne.Proj.projH _ g₁ ∈ E →
      CFSG.ComponentClassification.Burgoyne.Proj.projH _ g₂ ∈ E → g₁ * g₂ = g₂ * g₁
  · left
    obtain ⟨g, hgE, hg1, t, ht⟩ := exists_toral_good h E hE h27 hc
    exact ⟨g, hgE, hg1, le_trans ht (Finset.le_sup (f := eigMult (g : GL (Fin 6) K0))
      (Finset.mem_univ t))⟩
  · right
    obtain ⟨g₁, g₂, g₃, h1, h2, h3, h31, hκ, h13, h23, hdvd⟩ := exists_heis_triple h E hE h27 hc
    exact ⟨g₁, g₂, g₃, h1, h2, h3, h31, hκ, h13, h23, hdvd⟩

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
