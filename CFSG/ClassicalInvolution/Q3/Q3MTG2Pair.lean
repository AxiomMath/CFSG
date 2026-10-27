module

public import CFSG.ClassicalInvolution.Generic.SL2Involution

public section

namespace CFSG.ClassicalInvolution.Q3.Q3MT

open scoped MatrixGroups

theorem sl23_quat_decide :
    ∀ a₁ a₂ : SL(2, ZMod 3),
      (a₁ * a₁ = a₂ * a₂ ∨ a₁ * a₁ = (-1 : SL(2, ZMod 3)) * (a₂ * a₂)) →
      ((a₁ * a₂) * (a₁ * a₂) = a₁ * a₁ ∨
        (a₁ * a₂) * (a₁ * a₂) = (-1 : SL(2, ZMod 3)) * (a₁ * a₁)) →
      (a₁ * a₂ * a₁⁻¹ * a₂⁻¹ = 1 ∨ a₁ * a₂ * a₁⁻¹ * a₂⁻¹ = -1) := by
  decide +kernel

theorem sl23_center_decide :
    ∀ a : SL(2, ZMod 3), (∀ C : SL(2, ZMod 3), C * a = a * C) → a = 1 ∨ a = -1 := by
  decide +kernel

theorem sl23_exists_quat :
    ∃ I J : SL(2, ZMod 3), I * I = -1 ∧ J * J = -1 ∧ (I * J) * (I * J) = -1 := by
  decide +kernel

theorem sl23_neg_one_mul_self : (-1 : SL(2, ZMod 3)) * -1 = 1 := by decide +kernel

theorem sl23_neg_one_ne_one : (-1 : SL(2, ZMod 3)) ≠ 1 := by decide +kernel

theorem commutator_eq_of_quat {G : Type*} [Group G] {i j c : G} (hi : i * i = c) (hj : j * j = c)
    (hij : (i * j) * (i * j) = c) (hc : c * c = 1) : i * j * i⁻¹ * j⁻¹ = c := by
  have hi' : i⁻¹ = i * c := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, hi, hc])
  have hj' : j⁻¹ = j * c := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, hj, hc])
  have hcj : c * j = j * c := by
    rw [← hj]
    group
  calc i * j * i⁻¹ * j⁻¹ = i * j * (i * c) * (j * c) := by rw [hi', hj']
    _ = i * j * i * (c * j) * c := by group
    _ = i * j * i * (j * c) * c := by rw [hcj]
    _ = (i * j) * (i * j) * (c * c) := by group
    _ = c := by rw [hij, hc, mul_one]

variable {K : Type*} [Group K] {F' : Type} [Field F']

theorem eq_central_of_le_mul3 (h2 : (2 : F') ≠ 0) (ΦA : SL(2, ZMod 3) →* K)
    (ΦB : SL(2, F') →* K) (hA : Function.Injective ΦA) (hB : Function.Injective ΦB)
    (hcomm : ∀ A B, ΦA A * ΦB B = ΦB B * ΦA A) (hneg : ΦA (-1) = ΦB (-1))
    (Ψ : SL(2, ZMod 3) →* K) (hΨ : Function.Injective Ψ)
    (hS : ∀ A, ∃ a b, Ψ A = ΦA a * ΦB b) : Ψ (-1) = ΦB (-1) := by
  set Θ : SL(2, ZMod 3) × SL(2, F') →* K := ΦA.noncommCoprod ΦB (fun m n => hcomm m n) with hΘ
  have hΘapp : ∀ a b, Θ (a, b) = ΦA a * ΦB b := fun a b => rfl
  have hker : ∀ a b, ΦA a * ΦB b = 1 → a = 1 ∨ a = -1 := by
    intro a b hab
    apply sl23_center_decide
    intro C
    apply hA
    have h1 : ΦA a = (ΦB b)⁻¹ := eq_inv_of_mul_eq_one_left hab
    rw [map_mul, map_mul, h1]
    exact (Commute.inv_right (hcomm C b : Commute (ΦA C) (ΦB b))).eq
  obtain ⟨I, J, hI, hJ, hIJ⟩ := sl23_exists_quat
  have hc2 : Ψ (-1) * Ψ (-1) = 1 := by rw [← map_mul, sl23_neg_one_mul_self, map_one]
  have hc1 : Ψ (-1) ≠ 1 := fun h => sl23_neg_one_ne_one (hΨ (h.trans (map_one Ψ).symm))
  have hi : Ψ I * Ψ I = Ψ (-1) := by rw [← map_mul, hI]
  have hj : Ψ J * Ψ J = Ψ (-1) := by rw [← map_mul, hJ]
  have hij : (Ψ I * Ψ J) * (Ψ I * Ψ J) = Ψ (-1) := by rw [← map_mul, ← map_mul, hIJ]
  obtain ⟨a₁, b₁, h₁⟩ := hS I
  obtain ⟨a₂, b₂, h₂⟩ := hS J
  have hΘi : Θ (a₁, b₁) = Ψ I := h₁.symm
  have hΘj : Θ (a₂, b₂) = Ψ J := h₂.symm
  have e1 : ΦA (a₁ * a₁ * (a₂ * a₂)⁻¹) * ΦB (b₁ * b₁ * (b₂ * b₂)⁻¹) = 1 := by
    have : Θ ((a₁, b₁) * (a₁, b₁) * ((a₂, b₂) * (a₂, b₂))⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, map_mul, hΘi, hΘj, hi, hj, mul_inv_cancel]
    simpa [hΘapp] using this
  have f1 : a₁ * a₁ = a₂ * a₂ ∨ a₁ * a₁ = (-1 : SL(2, ZMod 3)) * (a₂ * a₂) := by
    rcases hker _ _ e1 with h | h
    · exact Or.inl (mul_inv_eq_one.mp h)
    · exact Or.inr (mul_inv_eq_iff_eq_mul.mp h)
  have e2 : ΦA ((a₁ * a₂) * (a₁ * a₂) * (a₁ * a₁)⁻¹) *
      ΦB ((b₁ * b₂) * (b₁ * b₂) * (b₁ * b₁)⁻¹) = 1 := by
    have : Θ (((a₁, b₁) * (a₂, b₂)) * ((a₁, b₁) * (a₂, b₂)) * ((a₁, b₁) * (a₁, b₁))⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_mul, hΘi, hΘj, hij, hi, mul_inv_cancel]
    simpa [hΘapp] using this
  have f2 : (a₁ * a₂) * (a₁ * a₂) = a₁ * a₁ ∨
      (a₁ * a₂) * (a₁ * a₂) = (-1 : SL(2, ZMod 3)) * (a₁ * a₁) := by
    rcases hker _ _ e2 with h | h
    · exact Or.inl (mul_inv_eq_one.mp h)
    · exact Or.inr (mul_inv_eq_iff_eq_mul.mp h)
  have hcomm_a := sl23_quat_decide a₁ a₂ f1 f2
  have hcij := commutator_eq_of_quat hi hj hij hc2
  have hprod : Ψ I * Ψ J * (Ψ I)⁻¹ * (Ψ J)⁻¹ =
      ΦA (a₁ * a₂ * a₁⁻¹ * a₂⁻¹) * ΦB (b₁ * b₂ * b₁⁻¹ * b₂⁻¹) := by
    rw [← hΘi, ← hΘj, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    simp [hΘapp]
  rw [hprod] at hcij
  obtain ⟨β, hβ⟩ : ∃ β : SL(2, F'), Ψ (-1) = ΦB β := by
    rcases hcomm_a with h | h
    · exact ⟨_, by rw [← hcij, h, map_one, one_mul]⟩
    · refine ⟨(-1) * (b₁ * b₂ * b₁⁻¹ * b₂⁻¹), ?_⟩
      rw [← hcij, h, hneg, ← map_mul]
  have hβ2 : β * β = 1 := by
    apply hB
    rw [map_mul, ← hβ, hc2, map_one]
  rcases CFSG.ClassicalInvolution.Generic.sl2_sq_eq_one h2 hβ2 with h | h
  · exact absurd (by rw [hβ, h, map_one]) hc1
  · rw [hβ, h]
