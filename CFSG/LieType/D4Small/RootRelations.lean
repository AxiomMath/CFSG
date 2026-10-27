module

public import CFSG.LieType.D4Small.WeightBasic
import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.LieType.D4Small.D4Datum

open scoped commutatorElement

variable {G : Type*} [Group G] {K : Type*} [Field K] [CharP K 2] (D : D4Datum G K)
  {X : Type*} [AddCommGroup X] [Module K X] (ρ : Representation K G X)

@[expose] def IsRootForm (E : (Fin 4 → ℤ) → Module.End K X) (j : ℕ) : Prop :=
  ∀ α, IsD4Root α → ∀ c : K, ρ (D.x α c) = 1 + c ^ (2 ^ j) • E α

theorem IsRootForm.mul_self {D : D4Datum G K} {ρ : Representation K G X}
    {E : (Fin 4 → ℤ) → Module.End K X} {j : ℕ}
    (h : IsRootForm D ρ E j) {α : Fin 4 → ℤ} (hα : IsD4Root α) : E α * E α = 0 := by
  have h1 : ρ (D.x α 1) = 1 + E α := by simpa using h α hα 1
  have h2 : (1 + E α) * (1 + E α) = 1 := by
    have hx := congrArg (fun g => ρ g) (D.x_add α hα 1 1)
    rw [CharTwo.add_self_eq_zero (1 : K), D.x_zero hα, map_one, map_mul, h1] at hx
    exact hx.symm
  have h3 : (1 + E α) * (1 + E α) = 1 + E α * E α := by
    calc (1 + E α) * (1 + E α) = 1 + (E α + E α) + E α * E α := by noncomm_ring
      _ = 1 + E α * E α := by rw [add_self_eq_zero K (E α), add_zero]
  rw [h3] at h2
  exact add_left_cancel (a := (1 : Module.End K X)) (b := E α * E α) (c := 0)
    (by simpa using h2)

theorem IsRootForm.rho_x_inv {D : D4Datum G K} {ρ : Representation K G X}
    {E : (Fin 4 → ℤ) → Module.End K X} {j : ℕ}
    (h : IsRootForm D ρ E j) {α : Fin 4 → ℤ} (hα : IsD4Root α) (c : K) :
    ρ ((D.x α c)⁻¹) = ρ (D.x α c) := by
  simpa [CharTwo.neg_eq] using (congrArg (fun g => ρ g) (D.x_neg hα c)).symm

theorem eq_zero_of_add_eq_zero_of_smul_add_smul_eq_zero {M : Type*} [AddCommGroup M]
    [Module K M] {μ : K} (hμ0 : μ ≠ 0) (hμ1 : μ ≠ 1) {P Q : M}
    (h1 : P + Q = 0) (h2 : μ • P + μ ^ 2 • Q = 0) : P = 0 ∧ Q = 0 := by
  have hQ : Q = -P := by
    rw [eq_neg_iff_add_eq_zero]
    rwa [add_comm]
  rw [hQ] at h2
  have h3 : (μ - μ ^ 2) • P = 0 := by
    rw [smul_neg, ← sub_eq_add_neg, ← sub_smul] at h2
    exact h2
  have hcoef : μ - μ ^ 2 = μ * (1 - μ) := by ring
  rw [hcoef] at h3
  have h4 : (1 - μ) • P = 0 := by
    rw [mul_smul] at h3
    exact (smul_eq_zero.mp h3).resolve_left hμ0
  have hP : P = 0 :=
    (smul_eq_zero.mp h4).resolve_left (sub_ne_zero.mpr (Ne.symm hμ1))
  refine ⟨hP, ?_⟩
  rw [hQ, hP, neg_zero]

theorem pow_two_pow_ne_zero_ne_one {μ : K} (hμ0 : μ ≠ 0) (hμ1 : μ ≠ 1) (j : ℕ) :
    μ ^ (2 ^ j) ≠ 0 ∧ μ ^ (2 ^ j) ≠ 1 := by
  refine ⟨pow_ne_zero _ hμ0, ?_⟩
  intro h
  have h2 : (μ - 1) ^ (2 ^ j) = 0 := by
    rw [sub_pow_char_pow, h, one_pow, sub_self]
  exact pow_ne_zero _ (sub_ne_zero.mpr hμ1) h2

theorem mul_four_expand (A B : Module.End K X) (u v : K)
    (hA : A * A = 0) (hB : B * B = 0) :
    (1 + u • A) * (1 + v • B) * (1 + u • A) * (1 + v • B) =
      1 + (u * v) • (A * B + B * A) + (u * v ^ 2) • (B * A * B) +
        (u ^ 2 * v) • (A * B * A) + (u ^ 2 * v ^ 2) • (A * B * A * B) := by
  have hABB : A * B * B = 0 := by rw [mul_assoc, hB, mul_zero]
  simp only [mul_add, add_mul, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_smul,
    smul_add, smul_zero, hA, hB, hABB, mul_zero, zero_mul, add_zero, zero_add]
  match_scalars
  all_goals try simp only [CharTwo.add_self_eq_zero]
  all_goals ring

private theorem IsRootForm.four_mul_eq {D : D4Datum G K} {ρ : Representation K G X}
    {E : (Fin 4 → ℤ) → Module.End K X} {j : ℕ} (h : IsRootForm D ρ E j)
    {α β : Fin 4 → ℤ} (hα : IsD4Root α) (hβ : IsD4Root β) (hαβ : α ⬝ᵥ β = -1)
    (c d : K) :
    1 + (c ^ (2 ^ j) * d ^ (2 ^ j)) • (E α * E β + E β * E α) +
        (c ^ (2 ^ j) * (d ^ (2 ^ j)) ^ 2) • (E β * E α * E β) +
        ((c ^ (2 ^ j)) ^ 2 * d ^ (2 ^ j)) • (E α * E β * E α) +
        ((c ^ (2 ^ j)) ^ 2 * (d ^ (2 ^ j)) ^ 2) • (E α * E β * E α * E β) =
      1 + (c ^ (2 ^ j) * d ^ (2 ^ j)) • E (α + β) := by
  have hA : E α * E α = 0 := IsRootForm.mul_self h hα
  have hB : E β * E β = 0 := IsRootForm.mul_self h hβ
  have hcomm : (1 + c ^ (2 ^ j) • E α) * (1 + d ^ (2 ^ j) • E β) *
      (1 + c ^ (2 ^ j) • E α) * (1 + d ^ (2 ^ j) • E β) =
      1 + (c ^ (2 ^ j) * d ^ (2 ^ j)) • E (α + β) := by
    have hc := congrArg (fun g => ρ g) (D.comm_eq α β hα hβ hαβ c d)
    simp only [commutatorElement_def, map_mul, IsRootForm.rho_x_inv h hα c,
      IsRootForm.rho_x_inv h hβ d, h α hα c, h β hβ d] at hc
    rw [h (α + β) (IsD4Root.add hα hβ hαβ) (c * d), mul_pow] at hc
    exact hc
  rw [← mul_four_expand (E α) (E β) (c ^ (2 ^ j)) (d ^ (2 ^ j)) hA hB]
  exact hcomm

private theorem IsRootForm.hzero {D : D4Datum G K} {ρ : Representation K G X}
    {E : (Fin 4 → ℤ) → Module.End K X} {j : ℕ} (h : IsRootForm D ρ E j)
    {α β : Fin 4 → ℤ} (hα : IsD4Root α) (hβ : IsD4Root β) (hαβ : α ⬝ᵥ β = -1)
    (c d : K) :
    c ^ (2 ^ j) •
        (d ^ (2 ^ j) • (E α * E β + E β * E α - E (α + β)) +
          (d ^ (2 ^ j)) ^ 2 • (E β * E α * E β)) +
      (c ^ (2 ^ j)) ^ 2 •
        (d ^ (2 ^ j) • (E α * E β * E α) +
          (d ^ (2 ^ j)) ^ 2 • (E α * E β * E α * E β)) = 0 := by
  have h := IsRootForm.four_mul_eq h hα hβ hαβ c d
  rw [show c ^ (2 ^ j) •
        (d ^ (2 ^ j) • (E α * E β + E β * E α - E (α + β)) +
          (d ^ (2 ^ j)) ^ 2 • (E β * E α * E β)) +
      (c ^ (2 ^ j)) ^ 2 •
        (d ^ (2 ^ j) • (E α * E β * E α) +
          (d ^ (2 ^ j)) ^ 2 • (E α * E β * E α * E β)) =
      (1 + (c ^ (2 ^ j) * d ^ (2 ^ j)) • (E α * E β + E β * E α) +
          (c ^ (2 ^ j) * (d ^ (2 ^ j)) ^ 2) • (E β * E α * E β) +
          ((c ^ (2 ^ j)) ^ 2 * d ^ (2 ^ j)) • (E α * E β * E α) +
          ((c ^ (2 ^ j)) ^ 2 * (d ^ (2 ^ j)) ^ 2) • (E α * E β * E α * E β)) -
        (1 + (c ^ (2 ^ j) * d ^ (2 ^ j)) • E (α + β)) by module]
  rw [h, sub_self]

private theorem eq_zero_of_four_smul_eq_zero {M : Type*} [AddCommGroup M] [Module K M]
    {w : K} (hw0 : w ≠ 0) (hw1 : w ≠ 1) {M1 M2 M3 M4 : M}
    (h11 : (M1 + M2) + (M3 + M4) = 0)
    (h21 : w • (M1 + M2) + w ^ 2 • (M3 + M4) = 0)
    (h12 : (w • M1 + w ^ 2 • M2) + (w • M3 + w ^ 2 • M4) = 0)
    (h22 : w • (w • M1 + w ^ 2 • M2) + w ^ 2 • (w • M3 + w ^ 2 • M4) = 0) :
    M1 = 0 ∧ M3 = 0 := by
  obtain ⟨hP1, hQ1⟩ := eq_zero_of_add_eq_zero_of_smul_add_smul_eq_zero hw0 hw1 h11 h21
  obtain ⟨hPw, hQw⟩ := eq_zero_of_add_eq_zero_of_smul_add_smul_eq_zero hw0 hw1 h12 h22
  exact ⟨(eq_zero_of_add_eq_zero_of_smul_add_smul_eq_zero hw0 hw1 hP1 hPw).1,
    (eq_zero_of_add_eq_zero_of_smul_add_smul_eq_zero hw0 hw1 hQ1 hQw).1⟩

private theorem IsRootForm.add_eq_and_mul_mul_eq_zero {D : D4Datum G K}
    {ρ : Representation K G X} {E : (Fin 4 → ℤ) → Module.End K X}
    {j : ℕ} (h : IsRootForm D ρ E j) (hK : ∃ μ : K, μ ≠ 0 ∧ μ ≠ 1)
    {α β : Fin 4 → ℤ} (hα : IsD4Root α) (hβ : IsD4Root β) (hαβ : α ⬝ᵥ β = -1) :
    E (α + β) = E α * E β + E β * E α ∧ E α * E β * E α = 0 := by
  obtain ⟨μ, hμ0, hμ1⟩ := hK
  set w : K := μ ^ (2 ^ j) with hw
  have hw0 : w ≠ 0 := (pow_two_pow_ne_zero_ne_one hμ0 hμ1 j).1
  have hw1 : w ≠ 1 := (pow_two_pow_ne_zero_ne_one hμ0 hμ1 j).2
  let M1 : Module.End K X := E α * E β + E β * E α - E (α + β)
  let M2 : Module.End K X := E β * E α * E β
  let M3 : Module.End K X := E α * E β * E α
  let M4 : Module.End K X := E α * E β * E α * E β
  have h11 : (M1 + M2) + (M3 + M4) = 0 := by
    have h := IsRootForm.hzero h hα hβ hαβ 1 1
    simpa [M1, M2, M3, M4] using h
  have h21 : w • (M1 + M2) + w ^ 2 • (M3 + M4) = 0 := by
    have h := IsRootForm.hzero h hα hβ hαβ μ 1
    rw [← hw] at h
    simpa [M1, M2, M3, M4] using h
  have h12 : (w • M1 + w ^ 2 • M2) + (w • M3 + w ^ 2 • M4) = 0 := by
    have h := IsRootForm.hzero h hα hβ hαβ 1 μ
    rw [← hw] at h
    simpa [M1, M2, M3, M4] using h
  have h22 : w • (w • M1 + w ^ 2 • M2) + w ^ 2 • (w • M3 + w ^ 2 • M4) = 0 := by
    have h := IsRootForm.hzero h hα hβ hαβ μ μ
    rw [← hw] at h
    simpa [M1, M2, M3, M4] using h
  obtain ⟨hM1, hM3⟩ := eq_zero_of_four_smul_eq_zero hw0 hw1 h11 h21 h12 h22
  refine ⟨?_, ?_⟩
  · simpa [M1] using (sub_eq_zero.mp hM1).symm
  · simpa [M3] using hM3

theorem IsRootForm.add_eq {D : D4Datum G K} {ρ : Representation K G X}
    {E : (Fin 4 → ℤ) → Module.End K X} {j : ℕ}
    (h : IsRootForm D ρ E j) (hK : ∃ μ : K, μ ≠ 0 ∧ μ ≠ 1)
    {α β : Fin 4 → ℤ} (hα : IsD4Root α) (hβ : IsD4Root β) (hαβ : α ⬝ᵥ β = -1) :
    E (α + β) = E α * E β + E β * E α :=
  (IsRootForm.add_eq_and_mul_mul_eq_zero h hK hα hβ hαβ).1

end CFSG.LieType.D4Small.D4Datum
