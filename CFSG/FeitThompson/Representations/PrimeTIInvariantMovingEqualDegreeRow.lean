module

public import CFSG.FeitThompson.Representations.PrimeComplementIrreducibleCases
import CFSG.FeitThompson.Representations.CentralFrobeniusFamilyDescription
import CFSG.FeitThompson.Representations.CentralLayerDegreeSquareDivisor

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {L : Type*} [Group L] {K W₁ W₂ : Subgroup L} [K.Normal]
  {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun L}

namespace IsPrimeCyclicTIHyp

section Fintype

variable [Fintype L] [Fintype ↥(W₁ ⊔ W₂)]

theorem primeTIres_ne_of_not_le_inertiaGroup (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) {β : ↥K → ℂ}
    (hβinv : ¬ W₁ ≤ inertiaGroup K β) (j : Irr ↥W₂) : h.primeTIres σ j ≠ β :=
  fun hj => hβinv (hj ▸ h.le_inertiaGroup_primeTIres hσ j)

omit [K.Normal] in
theorem ne_principalIrr_of_not_subset_charValueKernel (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) {H : Subgroup L} {j : Irr ↥W₂}
    (hker : ¬ (H.subgroupOf K : Set ↥K) ⊆ charValueKernel (h.primeTIres σ j)) :
    j ≠ principalIrr ↥W₂ := by
  intro hj0
  refine hker ?_
  rw [hj0, h.primeTIres_principal hσ, charValueKernel_one]
  exact Set.subset_univ _

omit [K.Normal] [Fintype ↥(W₁ ⊔ W₂)] in
theorem indClassFun_one_eq_primeTIrow_one [Fintype ↑(Irr ↥W₁)] (h : IsPrimeCyclicTIHyp K W₁ W₂)
    {α β : ↥K → ℂ} {j : Irr ↥W₂} (hdeg : α 1 = β 1) (hj : α = h.primeTIres σ j) :
    indClassFun K β 1 = h.primeTIrow σ j 1 := by
  rw [indClassFun_apply_one, h.primeTIrow_one, ← hj, ← hdeg, h.isComplement'_left.index_eq_card]

theorem exists_ne_principalIrr_primeTIres_eq_and_indClassFun_mem_Irr [Fintype ↑(Irr ↥W₁)]
    (h : IsPrimeCyclicTIHyp K W₁ W₂) (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ)
    (hq : (Nat.card ↥W₁).Prime) {H : Subgroup L} {α β : ↥K → ℂ}
    (hα : α ∈ Irr ↥K) (hβ : β ∈ Irr ↥K) (hdeg : α 1 = β 1)
    (hkerα : ¬ (H.subgroupOf K : Set ↥K) ⊆ charValueKernel α)
    (hkerβ : ¬ (H.subgroupOf K : Set ↥K) ⊆ charValueKernel β)
    (hαinv : W₁ ≤ inertiaGroup K α) (hβinv : ¬ W₁ ≤ inertiaGroup K β) :
    ∃ j : Irr ↥W₂, j ≠ principalIrr ↥W₂ ∧ α = h.primeTIres σ j ∧
      indClassFun K β ∈ Irr L ∧ indClassFun K β 1 = h.primeTIrow σ j 1 ∧
      (∀ (i : ↑(Irr ↥W₁)) (t : ↑(Irr ↥W₂)),
        IsOrthogonal (indClassFun K β) (h.primeTIirr σ i t)) ∧
      ¬ (H.subgroupOf K : Set ↥K) ⊆ charValueKernel β := by
  obtain ⟨j, hj⟩ := h.exists_primeTIres_eq hσ hq hα hαinv
  exact ⟨j, h.ne_principalIrr_of_not_subset_charValueKernel hσ (hj ▸ hkerα), hj,
    h.indClassFun_mem_Irr_of_not_le_inertiaGroup hq hβ hβinv,
    h.indClassFun_one_eq_primeTIrow_one hdeg hj,
    fun i t => h.isOrthogonal_indClassFun_primeTIirr hσ hβ
      (fun s => h.primeTIres_ne_of_not_le_inertiaGroup hσ hβinv s) i t, hkerβ⟩

end Fintype

end IsPrimeCyclicTIHyp

end CFSG.FeitThompson
