module

public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

section GmpGeneral

variable {G : Type*} [Group G]

theorem gmp_pow_conj_mem {Z : Subgroup G} {g : G} (hgZ : ∀ y ∈ Z, g * y * g⁻¹ ∈ Z) (n : ℕ) :
    ∀ y ∈ Z, g ^ n * y * (g ^ n)⁻¹ ∈ Z := by
  induction n with
  | zero => intro y hy; simpa using hy
  | succ n ih =>
    intro y hy
    have h1 := hgZ _ (ih y hy)
    rwa [show g * (g ^ n * y * (g ^ n)⁻¹) * g⁻¹ = g ^ (n + 1) * y * (g ^ (n + 1))⁻¹ by
      rw [pow_succ']; group] at h1

theorem gmp_pow_conj_eq {Z : Subgroup G} {g : G} {π : G → G}
    (hgZ : ∀ y ∈ Z, g * y * g⁻¹ ∈ Z) (hπg : ∀ y ∈ Z, π (g * y * g⁻¹) = g * π y * g⁻¹)
    (n : ℕ) : ∀ y ∈ Z, π (g ^ n * y * (g ^ n)⁻¹) = g ^ n * π y * (g ^ n)⁻¹ := by
  induction n with
  | zero => intro y _; simp
  | succ n ih =>
    intro y hy
    rw [show g ^ (n + 1) * y * (g ^ (n + 1))⁻¹ = g * (g ^ n * y * (g ^ n)⁻¹) * g⁻¹ by
      rw [pow_succ']; group, hπg _ (gmp_pow_conj_mem hgZ n y hy), ih y hy, pow_succ']
    group

theorem gmp_pow_conj_eq₂ {Z : Subgroup G} {g : G} {B : G → G → G}
    (hgZ : ∀ y ∈ Z, g * y * g⁻¹ ∈ Z)
    (hBg : ∀ y ∈ Z, ∀ y' ∈ Z, B (g * y * g⁻¹) (g * y' * g⁻¹) = g * B y y' * g⁻¹) (n : ℕ) :
    ∀ y ∈ Z, ∀ y' ∈ Z,
      B (g ^ n * y * (g ^ n)⁻¹) (g ^ n * y' * (g ^ n)⁻¹) = g ^ n * B y y' * (g ^ n)⁻¹ := by
  induction n with
  | zero => intro y _ y' _; simp
  | succ n ih =>
    intro y hy y' hy'
    have e : ∀ x : G, g ^ (n + 1) * x * (g ^ (n + 1))⁻¹ = g * (g ^ n * x * (g ^ n)⁻¹) * g⁻¹ :=
      fun x => by rw [pow_succ']; group
    rw [e, e, hBg _ (gmp_pow_conj_mem hgZ n y hy) _ (gmp_pow_conj_mem hgZ n y' hy'), ih y hy y' hy',
      pow_succ']
    group

theorem gmp_pairing_eq_of_pi_eq_right {Z : Subgroup G} {π : G → G} {B : G → G → G}
    (hπmul : ∀ y₁ ∈ Z, ∀ y₂ ∈ Z, π (y₁ * y₂) = π y₁ * π y₂)
    (hBr : ∀ y ∈ Z, ∀ y₁ ∈ Z, ∀ y₂ ∈ Z, B y (y₁ * y₂) = B y y₁ * B y y₂)
    (hB0r : ∀ y ∈ Z, π y = 1 → ∀ y' ∈ Z, B y' y = 1)
    {y y₁ y₂ : G} (hy : y ∈ Z) (hy₁ : y₁ ∈ Z) (hy₂ : y₂ ∈ Z) (he : π y₁ = π y₂) :
    B y y₁ = B y y₂ := by
  have hπ1 : π 1 = 1 := by
    have h := hπmul 1 (one_mem Z) 1 (one_mem Z)
    rw [one_mul] at h
    exact mul_eq_left.mp h.symm
  have hπinv : π y₁⁻¹ = (π y₁)⁻¹ := by
    have h := hπmul y₁⁻¹ (inv_mem hy₁) y₁ hy₁
    rw [inv_mul_cancel, hπ1] at h
    exact eq_inv_of_mul_eq_one_left h.symm
  have hδ : y₁⁻¹ * y₂ ∈ Z := mul_mem (inv_mem hy₁) hy₂
  have hπδ : π (y₁⁻¹ * y₂) = 1 := by
    rw [hπmul _ (inv_mem hy₁) _ hy₂, hπinv, he, inv_mul_cancel]
  calc B y y₁ = B y y₁ * B y (y₁⁻¹ * y₂) := by rw [hB0r _ hδ hπδ y hy, mul_one]
    _ = B y (y₁ * (y₁⁻¹ * y₂)) := (hBr _ hy _ hy₁ _ hδ).symm
    _ = B y y₂ := by rw [mul_inv_cancel_left]

theorem gmp_pairing_eq_of_pi_eq_left {Z : Subgroup G} {π : G → G} {B : G → G → G}
    (hπmul : ∀ y₁ ∈ Z, ∀ y₂ ∈ Z, π (y₁ * y₂) = π y₁ * π y₂)
    (hBl : ∀ y₁ ∈ Z, ∀ y₂ ∈ Z, ∀ y' ∈ Z, B (y₁ * y₂) y' = B y₁ y' * B y₂ y')
    (hB0l : ∀ y ∈ Z, π y = 1 → ∀ y' ∈ Z, B y y' = 1)
    {y y₁ y₂ : G} (hy : y ∈ Z) (hy₁ : y₁ ∈ Z) (hy₂ : y₂ ∈ Z) (he : π y₁ = π y₂) :
    B y₁ y = B y₂ y := by
  have hπ1 : π 1 = 1 := by
    have h := hπmul 1 (one_mem Z) 1 (one_mem Z)
    rw [one_mul] at h
    exact mul_eq_left.mp h.symm
  have hπinv : π y₁⁻¹ = (π y₁)⁻¹ := by
    have h := hπmul y₁⁻¹ (inv_mem hy₁) y₁ hy₁
    rw [inv_mul_cancel, hπ1] at h
    exact eq_inv_of_mul_eq_one_left h.symm
  have hδ : y₁⁻¹ * y₂ ∈ Z := mul_mem (inv_mem hy₁) hy₂
  have hπδ : π (y₁⁻¹ * y₂) = 1 := by
    rw [hπmul _ (inv_mem hy₁) _ hy₂, hπinv, he, inv_mul_cancel]
  calc B y₁ y = B y₁ y * B (y₁⁻¹ * y₂) y := by rw [hB0l _ hδ hπδ y hy, mul_one]
    _ = B (y₁ * (y₁⁻¹ * y₂)) y := (hBl _ hy₁ _ hδ _ hy).symm
    _ = B y₂ y := by rw [mul_inv_cancel_left]

theorem gmp_pairing_polar {A Z : Subgroup G} {π : G → G} {B : G → G → G} {g : G}
    (hπA : ∀ y ∈ Z, π y ∈ A)
    (hπmul : ∀ y₁ ∈ Z, ∀ y₂ ∈ Z, π (y₁ * y₂) = π y₁ * π y₂)
    (hBA : ∀ y ∈ Z, ∀ y' ∈ Z, B y y' ∈ A)
    (hBl : ∀ y₁ ∈ Z, ∀ y₂ ∈ Z, ∀ y' ∈ Z, B (y₁ * y₂) y' = B y₁ y' * B y₂ y')
    (hBr : ∀ y ∈ Z, ∀ y₁ ∈ Z, ∀ y₂ ∈ Z, B y (y₁ * y₂) = B y y₁ * B y y₂)
    (hB0l : ∀ y ∈ Z, π y = 1 → ∀ y' ∈ Z, B y y' = 1)
    (hB0r : ∀ y ∈ Z, π y = 1 → ∀ y' ∈ Z, B y' y = 1)
    (hgZ : ∀ y ∈ Z, g * y * g⁻¹ ∈ Z)
    (hπg : ∀ y ∈ Z, π (g * y * g⁻¹) = g * π y * g⁻¹)
    (hBg : ∀ y ∈ Z, ∀ y' ∈ Z, B (g * y * g⁻¹) (g * y' * g⁻¹) = g * B y y' * g⁻¹)
    (htr : ∀ a ∈ A, ∀ b ∈ A, a ≠ 1 → b ≠ 1 → ∃ n : ℕ, g ^ n * a * (g ^ n)⁻¹ = b)
    (j : ℕ) {y₁ y₂ : G} (hy₁ : y₁ ∈ Z) (hy₂ : y₂ ∈ Z) :
    B y₁ (g ^ j * y₂ * (g ^ j)⁻¹) * B y₂ (g ^ j * y₁ * (g ^ j)⁻¹) = 1 := by
  have hZn := gmp_pow_conj_mem hgZ
  have hπn := gmp_pow_conj_eq hgZ hπg
  have hBn := gmp_pow_conj_eq₂ hgZ hBg
  have hform : ∀ y₀ ∈ Z, ∀ y ∈ Z, π y₀ ≠ 1 → π y ≠ 1 → ∃ k : ℕ,
      π y = g ^ k * π y₀ * (g ^ k)⁻¹ ∧
        B y (g ^ j * y * (g ^ j)⁻¹) = g ^ k * B y₀ (g ^ j * y₀ * (g ^ j)⁻¹) * (g ^ k)⁻¹ := by
    intro y₀ hy₀ y hy hy₀1 hy1
    obtain ⟨k, hk⟩ := htr _ (hπA y₀ hy₀) _ (hπA y hy) hy₀1 hy1
    refine ⟨k, hk.symm, ?_⟩
    have hy₃ : g ^ k * y₀ * (g ^ k)⁻¹ ∈ Z := hZn k y₀ hy₀
    have hπy₃ : π (g ^ k * y₀ * (g ^ k)⁻¹) = π y := by rw [hπn k y₀ hy₀, hk]
    have hjy : g ^ j * y * (g ^ j)⁻¹ ∈ Z := hZn j y hy
    have hjy₃ : g ^ j * (g ^ k * y₀ * (g ^ k)⁻¹) * (g ^ j)⁻¹ ∈ Z := hZn j _ hy₃
    have hπj : π (g ^ j * (g ^ k * y₀ * (g ^ k)⁻¹) * (g ^ j)⁻¹) = π (g ^ j * y * (g ^ j)⁻¹) := by
      rw [hπn j _ hy₃, hπn j y hy, hπy₃]
    have hcomm : g ^ j * (g ^ k * y₀ * (g ^ k)⁻¹) * (g ^ j)⁻¹ =
        g ^ k * (g ^ j * y₀ * (g ^ j)⁻¹) * (g ^ k)⁻¹ := by
      group
    calc B y (g ^ j * y * (g ^ j)⁻¹)
        = B (g ^ k * y₀ * (g ^ k)⁻¹) (g ^ j * y * (g ^ j)⁻¹) :=
          gmp_pairing_eq_of_pi_eq_left hπmul hBl hB0l hjy hy hy₃ hπy₃.symm
      _ = B (g ^ k * y₀ * (g ^ k)⁻¹) (g ^ j * (g ^ k * y₀ * (g ^ k)⁻¹) * (g ^ j)⁻¹) :=
          gmp_pairing_eq_of_pi_eq_right hπmul hBr hB0r hy₃ hjy hjy₃ hπj.symm
      _ = g ^ k * B y₀ (g ^ j * y₀ * (g ^ j)⁻¹) * (g ^ k)⁻¹ := by
          rw [hcomm]
          exact hBn k y₀ hy₀ _ (hZn j y₀ hy₀)
  have hmul : B (y₁ * y₂) (g ^ j * (y₁ * y₂) * (g ^ j)⁻¹) =
      B y₁ (g ^ j * y₁ * (g ^ j)⁻¹) * B y₂ (g ^ j * y₂ * (g ^ j)⁻¹) := by
    by_cases hex : ∃ y₀ ∈ Z, π y₀ ≠ 1
    · obtain ⟨y₀, hy₀, hy₀1⟩ := hex
      by_cases hc1 : B y₀ (g ^ j * y₀ * (g ^ j)⁻¹) = 1
      · have hall : ∀ y ∈ Z, B y (g ^ j * y * (g ^ j)⁻¹) = 1 := by
          intro y hy
          by_cases hy1 : π y = 1
          · exact hB0l y hy hy1 _ (hZn j y hy)
          · obtain ⟨k, -, hk⟩ := hform y₀ hy₀ y hy hy₀1 hy1
            rw [hk, hc1]
            group
        rw [hall _ (mul_mem hy₁ hy₂), hall _ hy₁, hall _ hy₂, mul_one]
      · obtain ⟨i, hi⟩ := htr _ (hπA y₀ hy₀) _ (hBA _ hy₀ _ (hZn j y₀ hy₀)) hy₀1 hc1
        have hall : ∀ y ∈ Z, B y (g ^ j * y * (g ^ j)⁻¹) = g ^ i * π y * (g ^ i)⁻¹ := by
          intro y hy
          by_cases hy1 : π y = 1
          · rw [hB0l y hy hy1 _ (hZn j y hy), hy1]
            group
          · obtain ⟨k, hk1, hk⟩ := hform y₀ hy₀ y hy hy₀1 hy1
            rw [hk, ← hi, hk1]
            group
        rw [hall _ (mul_mem hy₁ hy₂), hall _ hy₁, hall _ hy₂, hπmul _ hy₁ _ hy₂]
        group
    · push Not at hex
      rw [hB0l _ (mul_mem hy₁ hy₂) (hex _ (mul_mem hy₁ hy₂)) _ (hZn j _ (mul_mem hy₁ hy₂)),
        hB0l _ hy₁ (hex _ hy₁) _ (hZn j _ hy₁), hB0l _ hy₂ (hex _ hy₂) _ (hZn j _ hy₂), mul_one]
  have hz₁ := hZn j y₁ hy₁
  have hz₂ := hZn j y₂ hy₂
  rw [show g ^ j * (y₁ * y₂) * (g ^ j)⁻¹ =
      (g ^ j * y₁ * (g ^ j)⁻¹) * (g ^ j * y₂ * (g ^ j)⁻¹) by group,
    hBl _ hy₁ _ hy₂ _ (mul_mem hz₁ hz₂), hBr _ hy₁ _ hz₁ _ hz₂, hBr _ hy₂ _ hz₁ _ hz₂] at hmul
  rw [mul_assoc] at hmul
  have h3 := mul_left_cancel hmul
  rw [← mul_assoc] at h3
  exact mul_right_cancel (h3.trans (one_mul _).symm)

theorem gmp_pairing_eq_one {A Z : Subgroup G} {π : G → G} {B : G → G → G} {g : G} {N : ℕ}
    (hN : Odd N) (hgN : g ^ N = 1)
    (hπA : ∀ y ∈ Z, π y ∈ A)
    (hπmul : ∀ y₁ ∈ Z, ∀ y₂ ∈ Z, π (y₁ * y₂) = π y₁ * π y₂)
    (hBA : ∀ y ∈ Z, ∀ y' ∈ Z, B y y' ∈ A)
    (hBl : ∀ y₁ ∈ Z, ∀ y₂ ∈ Z, ∀ y' ∈ Z, B (y₁ * y₂) y' = B y₁ y' * B y₂ y')
    (hBr : ∀ y ∈ Z, ∀ y₁ ∈ Z, ∀ y₂ ∈ Z, B y (y₁ * y₂) = B y y₁ * B y y₂)
    (hB0l : ∀ y ∈ Z, π y = 1 → ∀ y' ∈ Z, B y y' = 1)
    (hB0r : ∀ y ∈ Z, π y = 1 → ∀ y' ∈ Z, B y' y = 1)
    (hBd : ∀ y ∈ Z, B y y = 1)
    (hgZ : ∀ y ∈ Z, g * y * g⁻¹ ∈ Z)
    (hπg : ∀ y ∈ Z, π (g * y * g⁻¹) = g * π y * g⁻¹)
    (hBg : ∀ y ∈ Z, ∀ y' ∈ Z, B (g * y * g⁻¹) (g * y' * g⁻¹) = g * B y y' * g⁻¹)
    (htr : ∀ a ∈ A, ∀ b ∈ A, a ≠ 1 → b ≠ 1 → ∃ n : ℕ, g ^ n * a * (g ^ n)⁻¹ = b) :
    ∀ y ∈ Z, ∀ y' ∈ Z, B y y' = 1 := by
  intro y hy y' hy'
  by_cases h1 : π y = 1
  · exact hB0l y hy h1 y' hy'
  by_cases h2 : π y' = 1
  · exact hB0r y' hy' h2 y hy
  obtain ⟨k, hk⟩ := htr _ (hπA y hy) _ (hπA y' hy') h1 h2
  obtain ⟨a, ha⟩ : ∃ a : ℕ, g ^ (a + a) * π y * (g ^ (a + a))⁻¹ = π y' := by
    rcases Nat.even_or_odd k with ⟨a, rfl⟩ | ⟨l, rfl⟩
    · exact ⟨a, hk⟩
    · obtain ⟨m, rfl⟩ := hN
      refine ⟨l + m + 1, ?_⟩
      rw [show l + m + 1 + (l + m + 1) = (2 * l + 1) + (2 * m + 1) by ring, pow_add, hgN,
        mul_one]
      exact hk
  have hZn := gmp_pow_conj_mem hgZ
  have hy₂ : g ^ a * y * (g ^ a)⁻¹ ∈ Z := hZn a y hy
  have hp := gmp_pairing_polar hπA hπmul hBA hBl hBr hB0l hB0r hgZ hπg hBg htr a hy hy₂
  rw [hBd _ hy₂, mul_one,
    show g ^ a * (g ^ a * y * (g ^ a)⁻¹) * (g ^ a)⁻¹ = g ^ (a + a) * y * (g ^ (a + a))⁻¹ by
      rw [pow_add]; group] at hp
  rw [gmp_pairing_eq_of_pi_eq_right hπmul hBr hB0r hy hy' (hZn (a + a) y hy)
    (by rw [gmp_pow_conj_eq hgZ hπg (a + a) y hy, ha])]
  exact hp

end GmpGeneral

end CFSG.SeitzReduction.RankOne
