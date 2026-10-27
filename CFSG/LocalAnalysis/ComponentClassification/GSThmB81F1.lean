module

public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrOddTimesTwoTransport
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOrbitLocation

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

theorem Eight.le_normalizer_of_commute₂ {G : Type*} [Group G] {A B : Subgroup G}
    (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) : B ≤ normalizer (A : Set G) := by
  intro y hy
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rwa [← hAB x hx y hy, mul_inv_cancel_right]
  · intro hx
    have h1 := hAB _ hx y hy
    have h2 : x = y * x * y⁻¹ := by
      calc x = y⁻¹ * (y * x * y⁻¹ * y) := by group
        _ = y⁻¹ * (y * (y * x * y⁻¹)) := by rw [h1]
        _ = y * x * y⁻¹ := by group
    rw [h2]
    exact hx

theorem Eight.exists_mul_of_mem_sup₂ {G : Type*} [Group G] {A B : Subgroup G}
    (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ y ∈ A, ∃ w ∈ B, x = y * w := by
  have hx' : x ∈ ((A ⊔ B : Subgroup G) : Set G) := hx
  rw [coe_mul_of_right_le_normalizer_left A B (Eight.le_normalizer_of_commute₂ hAB)] at hx'
  obtain ⟨y, hy, w, hw, rfl⟩ := hx'
  exact ⟨y, hy, w, hw, rfl⟩

theorem eq_sup_inf_of_elemAb {G : Type*} [Group G] [Finite G] {A B E : Subgroup G}
    (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) (hdisj : A ⊓ B = ⊥) (hE : E ≤ A ⊔ B)
    (hE2 : ∀ e ∈ E, e * e = 1) {mA mB : ℕ}
    (hA : ∀ X : Subgroup G, X ≤ A → (∀ x ∈ X, x * x = 1) → Nat.card X ≤ mA)
    (hB : ∀ X : Subgroup G, X ≤ B → (∀ x ∈ X, x * x = 1) → Nat.card X ≤ mB)
    (hcard : mA * mB ≤ Nat.card E) : E = (E ⊓ A) ⊔ (E ⊓ B) := by
  let EA : Subgroup G :=
    { carrier := {x | x ∈ A ∧ ∃ y ∈ B, x * y ∈ E}
      mul_mem' := by
        rintro x x' ⟨hx, y, hy, hxy⟩ ⟨hx', y', hy', hxy'⟩
        refine ⟨mul_mem hx hx', y * y', mul_mem hy hy', ?_⟩
        have := mul_mem hxy hxy'
        rwa [show x * y * (x' * y') = x * x' * (y * y') by
          rw [mul_assoc x y, ← mul_assoc y, ← hAB x' hx' y hy]; group] at this
      one_mem' := ⟨one_mem _, 1, one_mem _, by simp⟩
      inv_mem' := by
        rintro x ⟨hx, y, hy, hxy⟩
        refine ⟨inv_mem hx, y⁻¹, inv_mem hy, ?_⟩
        have := inv_mem hxy
        rwa [mul_inv_rev, ← hAB _ (inv_mem hx) _ (inv_mem hy)] at this }
  let EB : Subgroup G :=
    { carrier := {y | y ∈ B ∧ ∃ x ∈ A, x * y ∈ E}
      mul_mem' := by
        rintro y y' ⟨hy, x, hx, hxy⟩ ⟨hy', x', hx', hxy'⟩
        refine ⟨mul_mem hy hy', x * x', mul_mem hx hx', ?_⟩
        have := mul_mem hxy hxy'
        rwa [show x * y * (x' * y') = x * x' * (y * y') by
          rw [mul_assoc x y, ← mul_assoc y, ← hAB x' hx' y hy]; group] at this
      one_mem' := ⟨one_mem _, 1, one_mem _, by simp⟩
      inv_mem' := by
        rintro y ⟨hy, x, hx, hxy⟩
        refine ⟨inv_mem hy, x⁻¹, inv_mem hx, ?_⟩
        have := inv_mem hxy
        rwa [mul_inv_rev, ← hAB _ (inv_mem hx) _ (inv_mem hy)] at this }
  have hsq : ∀ x ∈ A, ∀ y ∈ B, x * y ∈ E → x * x = 1 ∧ y * y = 1 := by
    intro x hx y hy hxy
    have h1 := hE2 _ hxy
    have h2 : x * x = (y * y)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      calc x * x * (y * y) = x * (x * y) * y := by group
        _ = x * (y * x) * y := by rw [hAB x hx y hy]
        _ = x * y * (x * y) := by group
        _ = 1 := h1
    have h3 : x * x ∈ A ⊓ B := mem_inf.mpr ⟨mul_mem hx hx, h2 ▸ inv_mem (mul_mem hy hy)⟩
    rw [hdisj, mem_bot] at h3
    refine ⟨h3, ?_⟩
    rw [h3, eq_comm, inv_eq_one] at h2
    exact h2
  have hEA2 : ∀ x ∈ EA, x * x = 1 := fun x ⟨hx, y, hy, hxy⟩ => (hsq x hx y hy hxy).1
  have hEB2 : ∀ y ∈ EB, y * y = 1 := fun y ⟨hy, x, hx, hxy⟩ => (hsq x hx y hy hxy).2
  have hcA := hA EA (fun x hx => hx.1) hEA2
  have hcB := hB EB (fun y hy => hy.1) hEB2
  have hle : E ≤ EA ⊔ EB := by
    intro e he
    obtain ⟨x, hx, y, hy, rfl⟩ := Eight.exists_mul_of_mem_sup₂ hAB (hE he)
    exact mul_mem_sup ⟨hx, y, hy, he⟩ ⟨hy, x, hx, he⟩
  have hc : ∀ x ∈ EA, ∀ y ∈ EB, x * y = y * x := fun x hx y hy => hAB x hx.1 y hy.1
  have h1 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute EA EB hc).1
  have h2 : Nat.card ↥(EA ⊔ EB) ≤ Nat.card E := by
    have h3 : Nat.card ↥(EA ⊔ EB) ≤ Nat.card ↥(EA ⊔ EB) * Nat.card ↥(EA ⊓ EB) :=
      Nat.le_mul_of_pos_right _ Nat.card_pos
    rw [h1] at h3
    calc Nat.card ↥(EA ⊔ EB) ≤ Nat.card EA * Nat.card EB := h3
      _ ≤ mA * mB := Nat.mul_le_mul hcA hcB
      _ ≤ Nat.card E := hcard
  have heq : E = EA ⊔ EB := eq_of_le_of_card_ge hle h2
  refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  have hA' : EA ≤ E ⊓ A := fun x hx =>
    mem_inf.mpr ⟨heq ▸ (mem_sup_left hx : x ∈ EA ⊔ EB), hx.1⟩
  have hB' : EB ≤ E ⊓ B := fun y hy =>
    mem_inf.mpr ⟨heq ▸ (mem_sup_right hy : y ∈ EA ⊔ EB), hy.1⟩
  calc E = EA ⊔ EB := heq
    _ ≤ (E ⊓ A) ⊔ (E ⊓ B) := sup_le_sup hA' hB'

end CFSG.ComponentClassification.GSThmB
