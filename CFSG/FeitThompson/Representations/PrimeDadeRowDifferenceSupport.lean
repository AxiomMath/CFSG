module

public import CFSG.FeitThompson.Representations.PrimeTILocalBridgeSupportNorm
import CFSG.FeitThompson.Representations.NonprincipalRowSumsCoreCentralizers

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {L : Type*} [Group L] {K W₁ W₂ : Subgroup L}
  {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun L}

namespace IsPrimeCyclicTIHyp

variable [Fintype L] [Fintype ↥(W₁ ⊔ W₂)]

theorem primeTIirr_sub_eq_zero_of_notMem_bridgeSupport (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) {H : Subgroup L} [H.Normal] (hWH : W₂ ≤ H)
    {A : Set L}
    (hA : ∀ y ∈ H, y ≠ 1 → ((K ⊓ Subgroup.centralizer {y} : Subgroup L) : Set L) \ {1} ⊆ A)
    (i : Irr ↥W₁) {j k : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) (hk : k ≠ principalIrr ↥W₂)
    (hone : h.primeTIirr σ i j 1 = h.primeTIirr σ i k 1)
    {x : L} (hx : x ∉ bridgeSupport A W₁ W₂) :
    (h.primeTIirr σ i j - h.primeTIirr σ i k) x = 0 := by
  have hxA : x ∉ A := fun hc => hx (subset_bridgeSupport_left hc)
  have hxV : x ∉ cyclicTIsetConj W₁ W₂ := fun hc => hx (cyclicTIsetConj_subset_bridgeSupport hc)
  rw [Pi.sub_apply, sub_eq_zero]
  by_cases hx1 : x = 1
  ·
    subst hx1; exact hone
  by_cases hxK : x ∈ K
  ·
    have hres : ∀ m : Irr ↥W₂, m ≠ principalIrr ↥W₂ → h.primeTIirr σ i m x = 0 := by
      intro m hm
      have hval : h.primeTIirr σ i m x = h.primeTIres σ m ⟨x, hxK⟩ := by
        rw [← h.resClassFun_primeTIirr (σ := σ) i m, resClassFun_apply]
      rw [hval]
      refine h.primeTIres_eq_zero hσ hWH hA hm (g := ⟨x, hxK⟩) ?_
      rintro (hc | hc)
      · exact hxA hc
      · exact hx1 hc
    rw [hres j hj, hres k hk]
  ·
    have _ : Finite L := Finite.of_fintype L
    obtain ⟨g, y, hy, w, hw, hw1, hconj⟩ := exists_conj_eq_mul_of_notMem h hxK
    rcases eq_or_ne y 1 with rfl | hy1
    ·
      rw [one_mul] at hconj
      have hIsConj : IsConj x w := by
        rw [isConj_comm, isConj_iff]
        exact ⟨g, by rw [← hconj]; group⟩
      have hcfj := Irr_subset_classFun (h.primeTIirr_mem_Irr hσ i j)
      have hcfk := Irr_subset_classFun (h.primeTIirr_mem_Irr hσ i k)
      have hw' : (⟨w, hw⟩ : ↥W₁) ≠ 1 := fun hc => hw1 (by simpa using congrArg Subtype.val hc)
      rw [mem_classFun.1 hcfj x w hIsConj, mem_classFun.1 hcfk x w hIsConj,
        h.primeTIirr_apply_coe_left hσ i j hw', h.primeTIirr_apply_coe_left hσ i k hw',
        h.primeTISign_eq_of_primeTIirr_one_eq hσ i j k hone]
    ·
      exact absurd (mem_cyclicTIsetConj.2 ⟨g⁻¹, y * w,
        mul_mem_cyclicTIset h hy hy1 hw hw1, by rw [← hconj]; group⟩) hxV

theorem support_primeTIirr_sub_subset_bridgeSupport (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) {H : Subgroup L} [H.Normal] (hWH : W₂ ≤ H)
    {A : Set L}
    (hA : ∀ y ∈ H, y ≠ 1 → ((K ⊓ Subgroup.centralizer {y} : Subgroup L) : Set L) \ {1} ⊆ A)
    (i : Irr ↥W₁) {j k : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) (hk : k ≠ principalIrr ↥W₂)
    (hone : h.primeTIirr σ i j 1 = h.primeTIirr σ i k 1) :
    Function.support (h.primeTIirr σ i j - h.primeTIirr σ i k) ⊆ bridgeSupport A W₁ W₂ :=
  fun _ hx => not_imp_comm.1
    (h.primeTIirr_sub_eq_zero_of_notMem_bridgeSupport hσ hWH hA i hj hk hone) hx

end IsPrimeCyclicTIHyp

end CFSG.FeitThompson
