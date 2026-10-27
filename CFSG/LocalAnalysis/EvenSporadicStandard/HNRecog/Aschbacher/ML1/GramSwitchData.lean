module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.GramDefs

public section

namespace CFSG.EvenSporadicStandard.HNRecog.ML1

open CFSG.EvenSporadicStandard.HNRecog.Fpf

@[expose] def g₁ : A5 := ofSwaps [(2, 3), (3, 4)]

@[expose] def g₂ : A5 := ofSwaps [(0, 1), (3, 4)]

@[expose] def g₃ : A5 := ofSwaps [(0, 1), (1, 2)]

@[expose] def sw₂ : List A5 := [g₁, g₂, g₃]

@[expose] def sw₃ : List A5 := [1, g₁, g₂, g₃]

theorem orderOf_c₃ : orderOf c₃ = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  rw [orderOf_eq_prime_iff]
  exact ⟨by decide +kernel, by decide +kernel⟩

theorem closure_a₀_c₃ : Subgroup.closure ({a₀, c₃} : Set A5) = ⊤ := by
  set K := Subgroup.closure ({a₀, c₃} : Set A5) with hK
  have h5 : orderOf a₀ ∣ Nat.card K :=
    Subgroup.orderOf_dvd_natCard K (Subgroup.subset_closure (by simp))
  have h3 : orderOf c₃ ∣ Nat.card K :=
    Subgroup.orderOf_dvd_natCard K (Subgroup.subset_closure (by simp))
  rw [orderOf_a₀] at h5
  rw [orderOf_c₃] at h3
  have h15 : 15 ∣ Nat.card K := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h5 h3
  exact eq_top_of_fifteen_le_card (Nat.le_of_dvd Nat.card_pos h15)

theorem sw₂_F : ∀ y : A5, (y = a₀ ∨ y = c₃) → ∀ h : A5,
    (sw₂.map fun g => gramFn b₂ (g⁻¹ * (y⁻¹ * h * y))).sum = (sw₂.map fun g => gramFn b₂ (g⁻¹ * h)).sum := by
  decide +kernel

theorem sw₂_G : ∀ x : A5,
    (sw₂.map fun g => (sw₂.map fun g' => gramFn b₂ (g⁻¹ * x * g')).sum).sum = gramFn b₁ x := by
  decide +kernel

theorem sw₃_F : ∀ y : A5, (y = a₀ ∨ y = c₃) → ∀ h : A5,
    (sw₃.map fun g => gramFn b₃ (g⁻¹ * (y⁻¹ * h * y))).sum = (sw₃.map fun g => gramFn b₃ (g⁻¹ * h)).sum := by
  decide +kernel

theorem sw₃_G : ∀ x : A5,
    (sw₃.map fun g => (sw₃.map fun g' => gramFn b₃ (g⁻¹ * x * g')).sum).sum = gramFn b₁ x := by
  decide +kernel

end CFSG.EvenSporadicStandard.HNRecog.ML1
