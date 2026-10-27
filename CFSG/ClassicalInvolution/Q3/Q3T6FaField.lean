module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T6.Fa

open scoped MatrixGroups

section Field

variable {F : Type*} [Field F] [Finite F]

theorem eq_zero_or_one_or_neg_one (hF : Nat.card F = 3) (c : F) : c = 0 ∨ c = 1 ∨ c = -1 := by
  have := Fintype.ofFinite F
  have h1 : c ^ Fintype.card F = c := FiniteField.pow_card c
  rw [← Nat.card_eq_fintype_card, hF] at h1
  have h2 : c * ((c - 1) * (c + 1)) = 0 := by linear_combination h1
  rcases mul_eq_zero.mp h2 with h | h
  · exact Or.inl h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
    · exact Or.inr (Or.inr (eq_neg_of_add_eq_zero_left h))

theorem neg_one_ne_one (hF : Nat.card F = 3) : (-1 : F) ≠ 1 := by
  intro h
  have := Fintype.ofFinite F
  have h3 : 2 < Fintype.card F := by
    rw [← Nat.card_eq_fintype_card, hF]
    norm_num
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp h3
  have key : ∀ x : F, x = 0 ∨ x = 1 := fun x => by
    rcases eq_zero_or_one_or_neg_one hF x with h0 | h0 | h0
    · exact Or.inl h0
    · exact Or.inr h0
    · exact Or.inr (h0.trans h)
  rcases key a with rfl | rfl <;> rcases key b with rfl | rfl <;> rcases key c with rfl | rfl <;>
    simp_all

theorem two_ne_zero (hF : Nat.card F = 3) : (2 : F) ≠ 0 := by
  intro h
  exact neg_one_ne_one hF (by linear_combination (-1 : F) * h)

theorem ringEquiv_eq_refl (hF : Nat.card F = 3) (σ : F ≃+* F) : σ = RingEquiv.refl F := by
  ext c
  rcases eq_zero_or_one_or_neg_one hF c with rfl | rfl | rfl <;> simp

theorem center_specialLinear_eq_bot (hF : Nat.card F = 3) :
    Subgroup.center SL(3, F) = ⊥ := by
  refine eq_bot_iff.mpr fun A hA => ?_
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have hr1 : r = 1 := by
    rcases eq_zero_or_one_or_neg_one hF r with rfl | rfl | rfl
    · simp at hr
    · rfl
    · exact absurd (by linear_combination hr) (neg_one_ne_one hF)
  subst hr1
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrA]
  simp

end Field

theorem injective_of_center_eq_bot {S E : Type*} [Group S] [Group E] (θ : S →* E)
    (hZ : Subgroup.center S = ⊥) (hker : θ.ker ≤ Subgroup.center S) : Function.Injective θ :=
  (MonoidHom.ker_eq_bot_iff θ).mp (le_bot_iff.mp (hZ ▸ hker))

section Lift

variable {K₀ E : Type*} [Group K₀] [Group E] (θ : K₀ →* E) {R₀ : Subgroup K₀}

theorem mem_of_lift_of_injective (hθ : Function.Injective θ) {φ : MulAut E}
    (hφ : ∀ x ∈ R₀.map θ, φ x ∈ R₀.map θ) {α : K₀ →* K₀} (hα : ∀ x, θ (α x) = φ (θ x)) :
    ∀ r ∈ R₀, α r ∈ R₀ := by
  intro r hr
  obtain ⟨s, hs, hsθ⟩ := hφ (θ r) (Subgroup.mem_map_of_mem θ hr)
  have : α r = s := hθ (by rw [hα, hsθ])
  rw [this]
  exact hs

theorem mem_centralizer_of_map_of_injective (hθ : Function.Injective θ) {x : K₀}
    (hx : θ x ∈ Subgroup.centralizer (R₀.map θ : Set E)) :
    x ∈ Subgroup.centralizer (R₀ : Set K₀) := by
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have h1 := (Subgroup.mem_centralizer_iff.mp hx) (θ r) ⟨r, hr, rfl⟩
  exact hθ (by rw [map_mul, map_mul]; exact h1)

end Lift

end CFSG.ClassicalInvolution.Q3.Q3T6.Fa
