module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevInputs
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviInputs
public import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36Inputs
import CFSG.GroupTheory.SylowIntersectionControl.IsolatedPermSix
import CFSG.GroupTheory.NormalizerInterval

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.Quasithin CFSG.ABGLocalTools Subgroup

theorem GomiChevIsolated.exists_not_mem_normalizer (hIso : GomiChevIsolated)
    (hR1 : GomiChevRankOneOvergroups) (hR2 : GomiFact36Overgroups) {Γ : Type} [Group Γ]
    [Finite Γ] {A V T Q : Subgroup Γ}
    (hA : IsGomiChevTwo ↥A ∨ Nonempty (↥A ≃* Equiv.Perm (Fin 6))) (hV : IsPGroup 2 V)
    (hVA : V ≤ normalizer (A : Set Γ)) (hT : IsSylowOf 2 T A)
    (hVT : V ≤ normalizer (T : Set Γ)) (hiso : IsPIsolatedOver 2 (A ⊓ centralizer (V : Set Γ)) ⊥)
    (hTQ : A ⊓ normalizer (T : Set Γ) < Q) (hQA : Q < A) :
    ∃ a ∈ V, a ∉ normalizer (Q : Set Γ) := by
  rcases hA with hChev | hS6
  ·
    rcases hIso Γ A V hChev hV hVA hiso with hrank | ⟨hrank, hU⟩
    ·
      rcases hR1 Γ T A Q hT hChev hrank hTQ.le hQA.le with h | h
      · exact absurd h hTQ.ne'
      · exact absurd h hQA.ne
    ·
      obtain ⟨a, haV, P, hBP, hPA, haP⟩ := hU T hT hVT
      refine ⟨a, haV, ?_⟩
      exact not_mem_normalizer_of_three (hR2 Γ T A (isSylowOf_iff.1 hT) hChev hrank)
        (Subgroup.inf_normalizer_le_normalizer_inf
          ⟨hVA haV, Subgroup.le_normalizer (hVT haV)⟩)
        (hVA haV) ⟨hBP, hPA⟩ ⟨hTQ, hQA⟩ haP
  ·
    exact exists_not_mem_normalizer_of_mulEquiv_perm_six hS6.some hV hVA hT hVT hiso hTQ hQA

end CFSG.GroupTheory
