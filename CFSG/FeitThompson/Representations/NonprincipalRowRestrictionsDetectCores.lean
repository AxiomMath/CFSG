module

public import CFSG.FeitThompson.Representations.LocalCharacterRowsRestrictIrreducibly
import CFSG.FeitThompson.Representations.PrimeTIDegreeSignCongruence
import CFSG.FeitThompson.Representations.RegularRepresentationContainsIrreducibles
public import CFSG.FeitThompson.Definitions.KernelFilteredIrreducibleCharacters
public import CFSG.FeitThompson.Representations.FiniteOrderTraceCharacters

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

theorem apply_mul_eq_of_mem_Irr_of_apply_eq_apply_one {L : Type*} [Group L] [Finite L]
    {χ : L → ℂ} (hχ : χ ∈ Irr L) {y : L} (hy : χ y = χ 1) (x : L) : χ (x * y) = χ x := by
  obtain ⟨V, -, rfl⟩ := mem_Irr.1 hχ
  rw [fdRepCharacter_eq] at hy ⊢
  have h1 : Representation.character V.ρ y = (Module.finrank ℂ V.V : ℂ) := by
    rw [hy, Representation.char_one]
  have h2 : V.ρ y = 1 := (Representation.character_eq_finrank_iff_of_finite V.ρ).1 h1
  have h3 : V.ρ (x * y) = V.ρ x := by rw [map_mul, h2, mul_one]
  simp only [Representation.character, h3]

variable {L : Type*} [Group L] {K W₁ W₂ : Subgroup L}
  {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun L}

namespace IsPrimeCyclicTIHyp

variable [Fintype L] [Fintype ↥(W₁ ⊔ W₂)]

theorem exists_mem_right_primeTIres_ne (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    ∃ y : ↥K, (y : L) ∈ W₂ ∧ h.primeTIres σ j y ≠ h.primeTIres σ j 1 := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  have hcomm₂ := h.isCyclicTIPair.isMulCommutative_right
  have hμ : h.primeTIirr σ (principalIrr ↥W₁) j ∈ Irr L :=
    h.primeTIirr_principal_left_mem_Irr hσ j
  have hker : ∀ y : L, y ∈ W₂ → h.primeTIirr σ (principalIrr ↥W₁) j y
      = h.primeTIirr σ (principalIrr ↥W₁) j 1 := by
    intro y hy
    have hval := hcon ⟨y, h.right_le hy⟩ hy
    rwa [h.primeTIres_apply, h.primeTIres_one] at hval
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h.left_ne_bot
  have hxW₂ : (x : L) ∉ W₂ := fun hc => hx1 <| Subtype.ext <| by
    have hmem : (x : L) ∈ W₁ ⊓ W₂ := Subgroup.mem_inf.2 ⟨x.2, hc⟩
    rw [h.inf_left_right_eq_bot] at hmem
    simpa using hmem
  have hζ : ∀ y : ↥W₂, (j : ↥W₂ → ℂ) y = 1 := by
    intro y
    have hxy : ((x : L) * (y : L)) ∈ W₁ ⊔ W₂ :=
      mul_mem (le_sup_left (a := W₁) (b := W₂) x.2) (le_sup_right (a := W₁) (b := W₂) y.2)
    have hmemB : ((x : L) * (y : L)) ∈ primeTIset W₁ W₂ :=
      mem_primeTIset.2 ⟨hxy, fun hc => hxW₂ (by simpa using mul_mem hc (W₂.inv_mem y.2))⟩
    have h1 : h.primeTIirr σ (principalIrr ↥W₁) j ((x : L) * (y : L))
        = h.primeTIirr σ (principalIrr ↥W₁) j (x : L) :=
      apply_mul_eq_of_mem_Irr_of_apply_eq_apply_one hμ (hker _ y.2) _
    have h2 : h.primeTIirr σ (principalIrr ↥W₁) j ((x : L) * (y : L))
        = h.primeTISign σ j * ((principalIrr ↥W₁ : Irr ↥W₁) : ↥W₁ → ℂ) x
            * (j : ↥W₂ → ℂ) y := by
      rw [h.primeTIirr_apply_of_mem_primeTIset hσ (principalIrr ↥W₁) j
          (v := ⟨(x : L) * (y : L), hxy⟩) hmemB,
        h.isCyclicTIPair.prodChar_apply_mul _ _ x.2 y.2]
      ring
    have h3 : h.primeTIirr σ (principalIrr ↥W₁) j (x : L)
        = h.primeTISign σ j * ((principalIrr ↥W₁ : Irr ↥W₁) : ↥W₁ → ℂ) x :=
      h.primeTIirr_apply_coe_left hσ _ j hx1
    rw [h2, h3, coe_principalIrr] at h1
    simp only [Pi.one_apply, mul_one] at h1
    rcases h.primeTISign_eq_one_or_eq_neg_one (σ := σ) j with hδ | hδ <;>
      rw [hδ] at h1 <;> simpa using h1
  exact hj (Subtype.ext (by funext y; rw [coe_principalIrr]; simpa using hζ y))

theorem not_subset_charValueKernel_primeTIres_right (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    ¬ ((W₂.subgroupOf K : Set ↥K) ⊆ charValueKernel (h.primeTIres σ j)) := by
  intro hsub
  obtain ⟨y, hyW₂, hy⟩ := h.exists_mem_right_primeTIres_ne hσ hj
  exact hy (mem_charValueKernel.1 (hsub (Subgroup.mem_subgroupOf.2 hyW₂)))

theorem exists_mem_primeTIres_ne (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) {H : Subgroup L} (hWH : W₂ ≤ H)
    {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    ∃ y : ↥K, (y : L) ∈ H ∧ h.primeTIres σ j y ≠ h.primeTIres σ j 1 := by
  obtain ⟨y, hyW₂, hy⟩ := h.exists_mem_right_primeTIres_ne hσ hj
  exact ⟨y, hWH hyW₂, hy⟩

theorem not_subset_charValueKernel_primeTIres (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) {H : Subgroup L} (hWH : W₂ ≤ H)
    {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    ¬ ((H.subgroupOf K : Set ↥K) ⊆ charValueKernel (h.primeTIres σ j)) := by
  intro hsub
  obtain ⟨y, hyH, hy⟩ := h.exists_mem_primeTIres_ne hσ hWH hj
  exact hy (mem_charValueKernel.1 (hsub (Subgroup.mem_subgroupOf.2 hyH)))

end IsPrimeCyclicTIHyp

end CFSG.FeitThompson
