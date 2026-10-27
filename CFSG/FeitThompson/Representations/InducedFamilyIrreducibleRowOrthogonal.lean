module

public import CFSG.FeitThompson.Representations.LocalCharacterRowsRestrictIrreducibly
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
public import CFSG.FeitThompson.Representations.NormalCoreCharacterVanishing

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {L : Type*} [Group L] {K W₁ W₂ : Subgroup L}
  {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun L}

namespace IsPrimeCyclicTIHyp

variable [Fintype L] [Fintype ↥(W₁ ⊔ W₂)]

theorem cfInner_primeTIirr_primeTIrow [Fintype ↑(Irr ↥W₁)] (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (i : Irr ↥W₁) (j : Irr ↥W₂) :
    cfInner (h.primeTIirr σ i j) (h.primeTIrow σ j) = 1 := by
  classical
  rw [primeTIrow_def, cfInner_sum_right, Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
    (fun k _ hki => by rw [h.cfInner_primeTIirr hσ, if_neg (by simp [Ne.symm hki])]),
    h.cfInner_primeTIirr hσ, if_pos ⟨rfl, rfl⟩]

theorem primeTIrow_mem_indFam [Fintype ↑(Irr ↥W₁)] (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (j : Irr ↥W₂) :
    h.primeTIrow σ j ∈ indFam K (Irr ↥K) := by
  rw [← h.indClassFun_primeTIres hσ j]
  exact indClassFun_mem_indFam K (h.primeTIres_mem_Irr hσ j)

theorem ne_primeTIirr_of_mem_indFam (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) {ζ : L → ℂ}
    (hζS : ζ ∈ indFam K (Irr ↥K)) (hζ : ζ ∈ Irr L) (i : Irr ↥W₁) (j : Irr ↥W₂) :
    ζ ≠ h.primeTIirr σ i j := by
  have : Fintype ↑(Irr ↥W₁) := Fintype.ofFinite _
  have hnormal := h.normal
  intro hEq
  have h1 : cfInner ζ (h.primeTIrow σ j) = 1 := by
    rw [hEq]; exact h.cfInner_primeTIirr_primeTIrow hσ i j
  by_cases hne : ζ = h.primeTIrow σ j
  ·
    have hnorm := h.cfInner_self_primeTIrow hσ j
    rw [← hne, cfInner_self_of_mem_Irr hζ] at hnorm
    exact h.left_ne_bot (Subgroup.card_eq_one.1 (by exact_mod_cast hnorm.symm))
  · rw [NormalInducedFamily.cfInner_eq_zero_of_mem_indFam K hζS
      (h.primeTIrow_mem_indFam hσ j) hne] at h1
    exact zero_ne_one h1

theorem cfInner_primeTIirr_eq_zero_of_mem_indFam (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) {ζ : L → ℂ}
    (hζS : ζ ∈ indFam K (Irr ↥K)) (hζ : ζ ∈ Irr L) (i : Irr ↥W₁) (j : Irr ↥W₂) :
    cfInner ζ (h.primeTIirr σ i j) = 0 :=
  cfInner_eq_zero_of_mem_Irr hζ (h.primeTIirr_mem_Irr hσ i j)
    (h.ne_primeTIirr_of_mem_indFam hσ hζS hζ i j)

theorem cfInner_primeTIrow_eq_zero_of_mem_indFam [Fintype ↑(Irr ↥W₁)]
    (h : IsPrimeCyclicTIHyp K W₁ W₂) (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) {ζ : L → ℂ}
    (hζS : ζ ∈ indFam K (Irr ↥K)) (hζ : ζ ∈ Irr L) (j : Irr ↥W₂) :
    cfInner ζ (h.primeTIrow σ j) = 0 := by
  rw [primeTIrow_def, cfInner_sum_right]
  exact Finset.sum_eq_zero fun i _ => h.cfInner_primeTIirr_eq_zero_of_mem_indFam hσ hζS hζ i j

theorem cfInner_primeTIirr_eq_zero (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) {ζ : L → ℂ}
    (hζS : ζ ∈ indFam K (Irr ↥K \ {1})) (hζ : ζ ∈ Irr L)
    (_hζ1 : ζ 1 = (Nat.card ↥W₁ : ℂ)) (i : Irr ↥W₁) (j : Irr ↥W₂) :
    cfInner ζ (h.primeTIirr σ i j) = 0 :=
  h.cfInner_primeTIirr_eq_zero_of_mem_indFam hσ (indFam_mono K (fun _ hθ => hθ.1) hζS) hζ i j

theorem cfInner_primeTIrow_eq_zero [Fintype ↑(Irr ↥W₁)] (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) {ζ : L → ℂ}
    (hζS : ζ ∈ indFam K (Irr ↥K \ {1})) (hζ : ζ ∈ Irr L)
    (_hζ1 : ζ 1 = (Nat.card ↥W₁ : ℂ)) (j : Irr ↥W₂) :
    cfInner ζ (h.primeTIrow σ j) = 0 :=
  h.cfInner_primeTIrow_eq_zero_of_mem_indFam hσ (indFam_mono K (fun _ hθ => hθ.1) hζS) hζ j

theorem isOrthogonal_primeTIirr (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) {ζ : L → ℂ}
    (hζS : ζ ∈ indFam K (Irr ↥K \ {1})) (hζ : ζ ∈ Irr L)
    (hζ1 : ζ 1 = (Nat.card ↥W₁ : ℂ)) (i : Irr ↥W₁) (j : Irr ↥W₂) :
    IsOrthogonal ζ (h.primeTIirr σ i j) :=
  isOrthogonal_iff.2 (h.cfInner_primeTIirr_eq_zero hσ hζS hζ hζ1 i j)

theorem isOrthogonal_primeTIrow [Fintype ↑(Irr ↥W₁)] (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) {ζ : L → ℂ}
    (hζS : ζ ∈ indFam K (Irr ↥K \ {1})) (hζ : ζ ∈ Irr L)
    (hζ1 : ζ 1 = (Nat.card ↥W₁ : ℂ)) (j : Irr ↥W₂) :
    IsOrthogonal ζ (h.primeTIrow σ j) :=
  isOrthogonal_iff.2 (h.cfInner_primeTIrow_eq_zero hσ hζS hζ hζ1 j)

end IsPrimeCyclicTIHyp

end CFSG.FeitThompson
