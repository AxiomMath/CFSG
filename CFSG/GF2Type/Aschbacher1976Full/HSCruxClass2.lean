module


import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Commutator
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

open Subgroup
open scoped commutatorElement

namespace Class2

variable {R : Type*} [Group R] {κ η : R}

theorem central_of_mem (hκc : ∀ x : R, x * κ = κ * x) (hηc : ∀ x : R, x * η = η * x)
    {c : R} (hc : c = 1 ∨ c = κ ∨ c = η ∨ c = η * κ) (x : R) : x * c = c * x := by
  rcases hc with rfl | rfl | rfl | rfl
  · simp
  · exact hκc x
  · exact hηc x
  · calc x * (η * κ) = (x * η) * κ := by rw [mul_assoc]
      _ = η * (x * κ) := by rw [hηc x, mul_assoc]
      _ = η * (κ * x) := by rw [hκc x]
      _ = η * κ * x := by rw [mul_assoc]

section Bilinear

variable (hκc : ∀ x : R, x * κ = κ * x) (hηc : ∀ x : R, x * η = η * x)
  (hV : ∀ x y : R, ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = κ ∨ ⁅x, y⁆ = η ∨ ⁅x, y⁆ = η * κ)
include hκc hηc hV

theorem comm_central (x y z : R) : ⁅x, y⁆ * z = z * ⁅x, y⁆ :=
  (central_of_mem hκc hηc (hV x y) z).symm

theorem comm_mul_left (x₁ x₂ y : R) : ⁅x₁ * x₂, y⁆ = ⁅x₂, y⁆ * ⁅x₁, y⁆ := by
  have h := comm_central hκc hηc hV x₂ y x₁
  calc ⁅x₁ * x₂, y⁆ = x₁ * ⁅x₂, y⁆ * x₁⁻¹ * ⁅x₁, y⁆ := by
        simp only [commutatorElement_def]
        group
    _ = ⁅x₂, y⁆ * ⁅x₁, y⁆ := by rw [← h]; group

theorem comm_mul_right (x y₁ y₂ : R) : ⁅x, y₁ * y₂⁆ = ⁅x, y₁⁆ * ⁅x, y₂⁆ := by
  have h := comm_central hκc hηc hV x y₂ y₁
  calc ⁅x, y₁ * y₂⁆ = ⁅x, y₁⁆ * (y₁ * ⁅x, y₂⁆ * y₁⁻¹) := by
        simp only [commutatorElement_def]
        group
    _ = ⁅x, y₁⁆ * ⁅x, y₂⁆ := by rw [← h]; group

end Bilinear

theorem no_two_values (hκc : ∀ x : R, x * κ = κ * x) (hηc : ∀ x : R, x * η = η * x)
    (hV : ∀ x y : R, ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = κ ∨ ⁅x, y⁆ = η ∨ ⁅x, y⁆ = η * κ)
    (hη2 : η * η = 1) (hne : ∀ x y : R, ⁅x, y⁆ ≠ κ) {a b x y : R} (hab : ⁅a, b⁆ = η)
    (hxy : ⁅x, y⁆ = η * κ) : False := by
  have hηκη : η * κ * η = κ := by
    calc η * κ * η = η * (κ * η) := mul_assoc _ _ _
      _ = η * (η * κ) := by rw [hηc κ]
      _ = (η * η) * κ := (mul_assoc _ _ _).symm
      _ = κ := by rw [hη2, one_mul]
  have hηηκ : η * (η * κ) = κ := by rw [← mul_assoc, hη2, one_mul]
  have F1 : ⁅a * x, b⁆ = ⁅x, b⁆ * η := by rw [comm_mul_left hκc hηc hV a x b, hab]
  have F2 : ⁅a * x, y⁆ = (η * κ) * ⁅a, y⁆ := by rw [comm_mul_left hκc hηc hV a x y, hxy]
  have F3 : ⁅x, b * y⁆ = ⁅x, b⁆ * (η * κ) := by rw [comm_mul_right hκc hηc hV x b y, hxy]
  have F4 : ⁅a, b * y⁆ = η * ⁅a, y⁆ := by rw [comm_mul_right hκc hηc hV a b y, hab]
  have F5 : ⁅a * x, b * y⁆ = (⁅x, b⁆ * (η * κ)) * (η * ⁅a, y⁆) := by
    rw [comm_mul_left hκc hηc hV a x (b * y), F3, F4]
  have hq : ⁅x, b⁆ = 1 := by
    rcases hV x b with h | h | h | h
    · exact h
    · exact absurd h (hne x b)
    · exfalso
      have := F3
      rw [h, hηηκ] at this
      exact hne x (b * y) this
    · exfalso
      have := F1
      rw [h, hηκη] at this
      exact hne (a * x) b this
  have hp : ⁅a, y⁆ = 1 := by
    rcases hV a y with h | h | h | h
    · exact h
    · exact absurd h (hne a y)
    · exfalso
      have := F2
      rw [h, hηκη] at this
      exact hne (a * x) y this
    · exfalso
      have := F4
      rw [h, hηηκ] at this
      exact hne a (b * y) this
  rw [hq, hp, one_mul, mul_one, hηκη] at F5
  exact hne (a * x) (b * y) F5

theorem exists_subgroup_not_mem (hκc : ∀ x : R, x * κ = κ * x) (hηc : ∀ x : R, x * η = η * x)
    (hη2 : η * η = 1) (hκ1 : κ ≠ 1) (hη1 : η ≠ 1) (hηκ : η ≠ κ)
    (hV : ∀ x y : R, ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = κ ∨ ⁅x, y⁆ = η ∨ ⁅x, y⁆ = η * κ)
    (hne : ∀ x y : R, ⁅x, y⁆ ≠ κ) (hκ2 : κ * κ = 1) :
    ∃ C : Subgroup R, κ ∉ C ∧ ∀ x y : R, ⁅x, y⁆ ∈ C := by
  have key : ∀ c : R, c * c = 1 → κ ≠ c → ∃ C : Subgroup R, κ ∉ C ∧ ∀ x y : R,
      ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = c → ⁅x, y⁆ ∈ C := by
    intro c hc2 hκc'
    have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
    refine ⟨{ carrier := {x | x = 1 ∨ x = c}
              one_mem' := Or.inl rfl
              mul_mem' := fun {a b} ha hb => by
                rcases ha with ha | ha <;> rcases hb with hb | hb
                · exact Or.inl (by rw [ha, hb, mul_one])
                · exact Or.inr (by rw [ha, hb, one_mul])
                · exact Or.inr (by rw [ha, hb, mul_one])
                · exact Or.inl (by rw [ha, hb]; exact hc2)
              inv_mem' := fun {a} ha => by
                rcases ha with ha | ha
                · exact Or.inl (by rw [ha, inv_one])
                · exact Or.inr (by rw [ha, hci]) }, ?_, fun x y h => h⟩
    rintro (h | h)
    · exact hκ1 h
    · exact hκc' h
  by_cases hA : ∀ x y : R, ⁅x, y⁆ = 1
  · obtain ⟨C, hC, hC'⟩ := key η hη2 hηκ.symm
    exact ⟨C, hC, fun x y => hC' x y (Or.inl (hA x y))⟩
  · push Not at hA
    obtain ⟨a, b, hab⟩ := hA
    have hcη : ⁅a, b⁆ = η ∨ ⁅a, b⁆ = η * κ := by
      rcases hV a b with h | h | h | h
      · exact absurd h hab
      · exact absurd h (hne a b)
      · exact Or.inl h
      · exact Or.inr h
    have hηκ2 : η * κ * (η * κ) = 1 := by
      calc η * κ * (η * κ) = η * (κ * η) * κ := by simp only [mul_assoc]
        _ = η * (η * κ) * κ := by rw [hηc κ]
        _ = (η * η) * (κ * κ) := by simp only [mul_assoc]
        _ = 1 := by rw [hη2, hκ2, one_mul]
    have hc2 : ⁅a, b⁆ * ⁅a, b⁆ = 1 := by
      rcases hcη with h | h <;> rw [h]
      · exact hη2
      · exact hηκ2
    have hκc' : κ ≠ ⁅a, b⁆ := by
      rcases hcη with h | h <;> rw [h]
      · exact fun h' => hηκ h'.symm
      · intro h'
        apply hη1
        calc η = η * (κ * κ) := by rw [hκ2, mul_one]
          _ = (η * κ) * κ := by rw [mul_assoc]
          _ = κ * κ := by rw [← h']
          _ = 1 := hκ2
    obtain ⟨C, hC, hC'⟩ := key _ hc2 hκc'
    refine ⟨C, hC, fun x y => hC' x y ?_⟩
    by_contra hxy
    push Not at hxy
    rcases hV x y with h | h | h | h
    · exact hxy.1 h
    · exact hne x y h
    · rcases hcη with h' | h'
      · exact hxy.2 (h.trans h'.symm)
      · exact no_two_values hκc hηc hV hη2 hne h h'
    · rcases hcη with h' | h'
      · exact no_two_values hκc hηc hV hη2 hne h' h
      · exact hxy.2 (h.trans h'.symm)

end Class2

end CFSG.GF2Type.Aschbacher1976Full.HS

