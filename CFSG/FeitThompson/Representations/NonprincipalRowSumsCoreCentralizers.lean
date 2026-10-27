module

public import CFSG.FeitThompson.Representations.LocalCharacterRowsRestrictIrreducibly
import CFSG.FeitThompson.Representations.NonprincipalRowRestrictionsDetectCores
public import CFSG.FeitThompson.Representations.NormalCoreCharacterVanishing

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {L : Type*} [Group L] {K W₁ W₂ : Subgroup L}
  {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun L}

theorem mem_of_conj_image_eq_self {A : Set L}
    (hA : ∀ g : L, (fun a => g⁻¹ * a * g) '' A = A) (g : L) {a : L} (ha : a ∈ A) :
    g⁻¹ * a * g ∈ A := by
  rw [← hA g]
  exact ⟨a, ha, rfl⟩

namespace IsPrimeCyclicTIHyp

variable [Fintype L] [Fintype ↥(W₁ ⊔ W₂)]

theorem primeTIres_eq_zero (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) {H : Subgroup L} [H.Normal] (hWH : W₂ ≤ H)
    {A : Set L}
    (hA : ∀ y ∈ H, y ≠ 1 → ((K ⊓ Subgroup.centralizer {y} : Subgroup L) : Set L) \ {1} ⊆ A)
    {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) {g : ↥K} (hg : (g : L) ∉ A ∪ {1}) :
    h.primeTIres σ j g = 0 := by
  have hnormal : (H.subgroupOf K).Normal := ‹H.Normal›.subgroupOf K
  refine eq_zero_of_forall_mem_centralizer (H := H.subgroupOf K)
    (h.primeTIres_mem_Irr hσ j) ?_ ?_
  ·
    obtain ⟨y, hyH, hy⟩ := h.exists_mem_primeTIres_ne hσ hWH hj
    exact ⟨y, Subgroup.mem_subgroupOf.2 hyH, hy⟩
  ·
    intro y hy hcomm
    by_contra hy1
    have hyH : (y : L) ∈ H := Subgroup.mem_subgroupOf.1 hy
    have hy1' : (y : L) ≠ 1 := fun hc => hy1 (Subtype.ext hc)
    have hc : (y : L) * (g : L) = (g : L) * (y : L) := by
      simpa using congrArg (Subtype.val : ↥K → L) hcomm
    refine hg (Or.inl (hA _ hyH hy1' ⟨Subgroup.mem_inf.2 ⟨g.2,
      Subgroup.mem_centralizer_singleton_iff.2 hc.symm⟩, ?_⟩))
    exact fun hc1 => hg (Or.inr hc1)

theorem support_primeTIres_subset (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) {H : Subgroup L} [H.Normal] (hWH : W₂ ≤ H)
    {A : Set L}
    (hA : ∀ y ∈ H, y ≠ 1 → ((K ⊓ Subgroup.centralizer {y} : Subgroup L) : Set L) \ {1} ⊆ A)
    {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    Function.support (h.primeTIres σ j) ⊆ K.subtype ⁻¹' (A ∪ {1}) := fun g hg =>
  not_imp_comm.1 (h.primeTIres_eq_zero hσ hWH hA hj) hg

theorem primeTIrow_eq_zero [Fintype ↑(Irr ↥W₁)] (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) {H : Subgroup L} [H.Normal] (hWH : W₂ ≤ H)
    {A : Set L} (hAconj : ∀ t : L, (fun a => t⁻¹ * a * t) '' A = A)
    (hA : ∀ y ∈ H, y ≠ 1 → ((K ⊓ Subgroup.centralizer {y} : Subgroup L) : Set L) \ {1} ⊆ A)
    {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) {g : L} (hg : g ∉ A ∪ {1}) :
    h.primeTIrow σ j g = 0 := by
  classical
  rw [← h.indClassFun_primeTIres hσ, indClassFun_apply]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun t _ => ?_)
  by_cases hm : t⁻¹ * g * t ∈ K
  · rw [dif_pos hm]
    refine h.primeTIres_eq_zero hσ hWH hA hj (fun hcon => hg ?_)
    rcases hcon with hcon | hcon
    · have h2 := mem_of_conj_image_eq_self hAconj t⁻¹ hcon
      rw [show t⁻¹⁻¹ * (t⁻¹ * g * t) * t⁻¹ = g by group] at h2
      exact Or.inl h2
    · have h1 : t⁻¹ * g * t = 1 := hcon
      refine Or.inr ?_
      calc g = t * (t⁻¹ * g * t) * t⁻¹ := by group
        _ = 1 := by rw [h1]; group
  · rw [dif_neg hm]

theorem support_primeTIrow_subset [Fintype ↑(Irr ↥W₁)] (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) {H : Subgroup L} [H.Normal] (hWH : W₂ ≤ H)
    {A : Set L} (hAconj : ∀ t : L, (fun a => t⁻¹ * a * t) '' A = A)
    (hA : ∀ y ∈ H, y ≠ 1 → ((K ⊓ Subgroup.centralizer {y} : Subgroup L) : Set L) \ {1} ⊆ A)
    {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    Function.support (h.primeTIrow σ j) ⊆ A ∪ {1} := fun g hg =>
  not_imp_comm.1 (h.primeTIrow_eq_zero hσ hWH hAconj hA hj) hg

end IsPrimeCyclicTIHyp

end CFSG.FeitThompson
