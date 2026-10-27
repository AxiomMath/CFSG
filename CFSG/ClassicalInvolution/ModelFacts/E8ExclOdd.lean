module

public import CFSG.ClassicalInvolution.ModelFacts.E8ExclRoots

public section

namespace CFSG.ClassicalInvolution.ModelFacts.E7Model

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

theorem exists_odd_total_list : ∀ δ₁ ∈ rootList, ∀ δ₂ ∈ rootList, iform7 δ₁ δ₂ = 0 →
    ∃ j : Fin 7, Odd (iform7 δ₁ (Pi.single j 1) + iform7 δ₂ (Pi.single j 1)) := by
  decide +kernel

theorem exists_odd_total {δ₁ δ₂ : V7} (h₁ : IsRoot .E7 δ₁) (h₂ : IsRoot .E7 δ₂)
    (h : iform δ₁ δ₂ = 0) :
    ∃ j : Fin (Tag.rank .E7), Odd (iform δ₁ (Pi.single j 1) + iform δ₂ (Pi.single j 1)) := by
  rw [iform_eq_iform7] at h
  obtain ⟨j, hj⟩ := exists_odd_total_list δ₁ ((mem_rootList_iff _).2 h₁) δ₂
    ((mem_rootList_iff _).2 h₂) h
  exact ⟨j, by rw [iform_eq_iform7, iform_eq_iform7]; exact hj⟩

end CFSG.ClassicalInvolution.ModelFacts.E7Model
