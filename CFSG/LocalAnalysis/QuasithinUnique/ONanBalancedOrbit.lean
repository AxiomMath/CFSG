module

public import CFSG.LocalAnalysis.QuasithinUnique.ONanBalanced
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.QuasithinUnique.ONan

open Module
open scoped Pointwise

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {X R : Subgroup (V ≃ₗ[ZMod 2] V)} {A C : Submodule (ZMod 2) V}

def orbR (R : Subgroup (V ≃ₗ[ZMod 2] V)) (D : Submodule (ZMod 2) V) :
    Set (Submodule (ZMod 2) V) :=
  Set.range fun ρ : R => (ρ : V ≃ₗ[ZMod 2] V) • D

theorem Balanced.orbR_subset (h : Balanced X R A C) {D : Submodule (ZMod 2) V}
    (hD : D ∈ MulAction.orbit X C \ {C, A}) :
    orbR R D ⊆ MulAction.orbit X C \ {C, A} := by
  rintro _ ⟨ρ, rfl⟩
  have hρR : (ρ : V ≃ₗ[ZMod 2] V) ∈ R := ρ.2
  refine ⟨smul_mem_orbit (h.setting.le hρR) hD.1, ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  constructor
  · intro heq
    apply hD.2
    left
    have : D = (ρ : V ≃ₗ[ZMod 2] V)⁻¹ • C := by rw [← heq, inv_smul_smul]
    rw [this]
    exact h.setting.smul_C (R.inv_mem hρR)
  · intro heq
    apply hD.2
    right
    have : D = (ρ : V ≃ₗ[ZMod 2] V)⁻¹ • A := by rw [← heq, inv_smul_smul]
    rw [this]
    exact h.setting.smul_A (R.inv_mem hρR)

theorem Balanced.orbR_inj (h : Balanced X R A C) {D : Submodule (ZMod 2) V}
    (hD : D ∈ MulAction.orbit X C \ {C, A}) :
    Function.Injective fun ρ : R => (ρ : V ≃ₗ[ZMod 2] V) • D := by
  intro ρ₁ ρ₂ heq
  by_contra hne
  have hne' : ((ρ₂⁻¹ * ρ₁ : R) : V ≃ₗ[ZMod 2] V) ≠ 1 := by
    intro h1
    apply hne
    have : (ρ₂⁻¹ * ρ₁ : R) = 1 := Subtype.ext h1
    exact (inv_mul_eq_one.mp this).symm
  have hρ : ((ρ₂⁻¹ * ρ₁ : R) : V ≃ₗ[ZMod 2] V) ∈ R := (ρ₂⁻¹ * ρ₁).2
  have heq' : (ρ₁ : V ≃ₗ[ZMod 2] V) • D = (ρ₂ : V ≃ₗ[ZMod 2] V) • D := heq
  have hfix : ((ρ₂⁻¹ * ρ₁ : R) : V ≃ₗ[ZMod 2] V) • D = D := by
    show ((ρ₂ : V ≃ₗ[ZMod 2] V)⁻¹ * (ρ₁ : V ≃ₗ[ZMod 2] V)) • D = D
    rw [mul_smul, heq', inv_smul_smul]
  have hDC : D ⊓ C = ⊥ :=
    h.inf_eq_bot_of_mem hD.1 (MulAction.mem_orbit_self C) (fun hDC => hD.2 (Or.inl hDC))
  have := eq_of_smul_eq h.setting h.finrank_eq h.free hρ hne' hDC
    ((finrank_orbit hD.1).trans h.finrank_eq.symm) hfix
  exact hD.2 (Or.inr this)

theorem Balanced.ncard_orbR (h : Balanced X R A C) {D : Submodule (ZMod 2) V}
    (hD : D ∈ MulAction.orbit X C \ {C, A}) :
    (orbR R D).ncard = 2 ^ finrank (ZMod 2) C - 1 := by
  have h1 := Set.ncard_range_of_injective (h.orbR_inj hD)
  have h2 := natCard_R h.setting h.free h.two_le_A
  rw [h.finrank_eq] at h2
  exact h1.trans h2

omit [Finite V] in
theorem disjoint_orbR {D E : Submodule (ZMod 2) V}
    (hED : E ∉ orbR R D) : Disjoint (orbR R E) (orbR R D) := by
  rw [Set.disjoint_left]
  rintro _ ⟨ρ₁, rfl⟩ ⟨ρ₂, hρ₂⟩
  apply hED
  refine ⟨ρ₁⁻¹ * ρ₂, ?_⟩
  have hρ₂' : (ρ₂ : V ≃ₗ[ZMod 2] V) • D = (ρ₁ : V ≃ₗ[ZMod 2] V) • E := hρ₂
  show ((ρ₁ : V ≃ₗ[ZMod 2] V)⁻¹ * (ρ₂ : V ≃ₗ[ZMod 2] V)) • D = E
  rw [mul_smul, hρ₂', inv_smul_smul]

theorem Balanced.ncard_diff_le (h : Balanced X R A C) :
    (MulAction.orbit X C \ {C, A}).ncard ≤ 2 ^ finrank (ZMod 2) C := by
  have hsub : insert C (MulAction.orbit X C \ {C, A}) ⊆ MulAction.orbit X C := by
    intro D hD
    rcases hD with rfl | hD
    · exact MulAction.mem_orbit_self _
    · exact hD.1
  have hnot : C ∉ MulAction.orbit X C \ {C, A} := fun hC => hC.2 (Or.inl rfl)
  have h1 := Set.ncard_le_ncard hsub
  rw [Set.ncard_insert_of_notMem hnot] at h1
  have h2 := h.ncard_orbit_le
  omega

theorem Balanced.card_diff (h : Balanced X R A C) :
    (MulAction.orbit X C \ {C, A}).ncard = 0 ∨
      (MulAction.orbit X C \ {C, A}).ncard = 2 ^ finrank (ZMod 2) C - 1 := by
  by_cases hT : MulAction.orbit X C \ {C, A} = ∅
  · left
    rw [hT]
    exact Set.ncard_empty _
  · right
    obtain ⟨D₀, hD₀⟩ := Set.nonempty_iff_ne_empty.mpr hT
    have hsub : orbR R D₀ ⊆ MulAction.orbit X C \ {C, A} := h.orbR_subset hD₀
    have hr4 : 4 ≤ 2 ^ finrank (ZMod 2) C := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ finrank (ZMod 2) C := Nat.pow_le_pow_right (by norm_num) h.two_le
    by_cases hall : MulAction.orbit X C \ {C, A} ⊆ orbR R D₀
    · have : MulAction.orbit X C \ {C, A} = orbR R D₀ := Set.Subset.antisymm hall hsub
      rw [this, h.ncard_orbR hD₀]
    · exfalso
      obtain ⟨E, hE, hED⟩ := Set.not_subset.mp hall
      have hdisj := disjoint_orbR (D := D₀) hED
      have hunion : orbR R E ∪ orbR R D₀ ⊆ MulAction.orbit X C \ {C, A} :=
        Set.union_subset (h.orbR_subset hE) hsub
      have h1 := Set.ncard_le_ncard hunion
      rw [Set.ncard_union_eq hdisj, h.ncard_orbR hE, h.ncard_orbR hD₀] at h1
      have h2 := h.ncard_diff_le
      omega

end CFSG.QuasithinUnique.ONan
