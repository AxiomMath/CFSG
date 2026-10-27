module

public import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

variable {Y : Type} [Group Y]

theorem szh1n_mem_sup {P₁ P₂ : Subgroup Y}
    (hcomm : ∀ u ∈ P₁, ∀ v ∈ P₂, u * v = v * u) {c : Y} (hc : c ∈ P₁ ⊔ P₂) :
    ∃ u₁ ∈ P₁, ∃ u₂ ∈ P₂, c = u₁ * u₂ := by
  let S : Subgroup Y :=
    { carrier := {c | ∃ u₁ ∈ P₁, ∃ u₂ ∈ P₂, c = u₁ * u₂}
      one_mem' := ⟨1, P₁.one_mem, 1, P₂.one_mem, (mul_one 1).symm⟩
      mul_mem' := by
        rintro _ _ ⟨a₁, ha₁, a₂, ha₂, rfl⟩ ⟨b₁, hb₁, b₂, hb₂, rfl⟩
        refine ⟨a₁ * b₁, P₁.mul_mem ha₁ hb₁, a₂ * b₂, P₂.mul_mem ha₂ hb₂, ?_⟩
        have h := hcomm b₁ hb₁ a₂ ha₂
        calc a₁ * a₂ * (b₁ * b₂) = a₁ * (a₂ * b₁) * b₂ := by simp only [mul_assoc]
          _ = a₁ * (b₁ * a₂) * b₂ := by rw [h]
          _ = a₁ * b₁ * (a₂ * b₂) := by simp only [mul_assoc]
      inv_mem' := by
        rintro _ ⟨a₁, ha₁, a₂, ha₂, rfl⟩
        refine ⟨a₁⁻¹, P₁.inv_mem ha₁, a₂⁻¹, P₂.inv_mem ha₂, ?_⟩
        rw [mul_inv_rev]
        exact (hcomm a₁⁻¹ (P₁.inv_mem ha₁) a₂⁻¹ (P₂.inv_mem ha₂)).symm }
  have hle : P₁ ⊔ P₂ ≤ S :=
    sup_le (fun u hu => ⟨u, hu, 1, P₂.one_mem, (mul_one u).symm⟩)
      (fun v hv => ⟨1, P₁.one_mem, v, hv, (one_mul v).symm⟩)
  exact hle hc

theorem szh1n_split {P₁ P₂ : Subgroup Y} (hdisj : P₁ ⊓ P₂ = ⊥)
    {a a' b b' : Y} (ha : a ∈ P₁) (ha' : a' ∈ P₁) (hb : b ∈ P₂) (hb' : b' ∈ P₂)
    (h : a * b = a' * b') : a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_inv_cancel_right]
  have h₁ : a'⁻¹ * a ∈ P₁ := P₁.mul_mem (P₁.inv_mem ha') ha
  have h₂ : a'⁻¹ * a ∈ P₂ := by
    rw [h1]
    exact P₂.mul_mem hb' (P₂.inv_mem hb)
  have hmem : a'⁻¹ * a ∈ P₁ ⊓ P₂ := Subgroup.mem_inf.2 ⟨h₁, h₂⟩
  rw [hdisj, Subgroup.mem_bot] at hmem
  refine ⟨(inv_mul_eq_one.1 hmem).symm, ?_⟩
  rw [hmem] at h1
  exact (mul_inv_eq_one.1 h1.symm).symm

theorem szh1n_pow_five {u : Y} (h25 : u ^ 25 = 1) {m : ℤ} (hm : u ^ m = 1)
    (h : ¬ (25 : ℤ) ∣ m) : u ^ 5 = 1 := by
  have hd25 : orderOf u ∣ 25 := orderOf_dvd_of_pow_eq_one h25
  have hdm : (orderOf u : ℤ) ∣ m := orderOf_dvd_iff_zpow_eq_one.2 hm
  have key : ∀ d : ℕ, d ∣ 25 → (d : ℤ) ∣ m → d ∣ 5 := by
    intro d hd hdm
    have hle : d ≤ 25 := Nat.le_of_dvd (by decide) hd
    have hcases : ∀ d : ℕ, d < 26 → d ∣ 25 → d = 1 ∨ d = 5 ∨ d = 25 := by decide
    rcases hcases d (by omega) hd with rfl | rfl | rfl
    · exact one_dvd 5
    · exact dvd_refl 5
    · exact absurd hdm h
  exact orderOf_dvd_iff_pow_eq_one.1 (key _ hd25 hdm)

theorem szh1_num_final {P₁ P₂ : Subgroup Y} {y c : Y}
    (hcomm : ∀ u ∈ P₁, ∀ v ∈ P₂, u * v = v * u) (hdisj : P₁ ⊓ P₂ = ⊥)
    (h25₁ : ∀ u ∈ P₁, u ^ 25 = 1) (h25₂ : ∀ u ∈ P₂, u ^ 25 = 1)
    {n₁ n₂ ν : ℤ} (hn₁ : ∀ u ∈ P₁, y * u * y⁻¹ = u ^ n₁)
    (hn₂ : ∀ u ∈ P₂, y * u * y⁻¹ = u ^ n₂)
    (hne : n₁ % 25 ≠ n₂ % 25)
    (hc : c ∈ P₁ ⊔ P₂) (hyc : y * c * y⁻¹ = c ^ ν) : c ^ 5 ∈ P₁ ∨ c ^ 5 ∈ P₂ := by
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := szh1n_mem_sup hcomm hc
  have hcm : Commute u₁ u₂ := hcomm u₁ hu₁ u₂ hu₂
  have hconj : y * (u₁ * u₂) * y⁻¹ = u₁ ^ n₁ * u₂ ^ n₂ := by
    rw [← hn₁ u₁ hu₁, ← hn₂ u₂ hu₂]
    simp only [mul_assoc, inv_mul_cancel_left]
  rw [hconj, hcm.mul_zpow] at hyc
  obtain ⟨e₁, e₂⟩ := szh1n_split hdisj (P₁.zpow_mem hu₁ n₁) (P₁.zpow_mem hu₁ ν)
    (P₂.zpow_mem hu₂ n₂) (P₂.zpow_mem hu₂ ν) hyc
  have f₁ : u₁ ^ (n₁ - ν) = 1 := by rw [zpow_sub, e₁, mul_inv_cancel]
  have f₂ : u₂ ^ (n₂ - ν) = 1 := by rw [zpow_sub, e₂, mul_inv_cancel]
  by_cases h25 : (25 : ℤ) ∣ n₁ - ν
  · have h25' : ¬ (25 : ℤ) ∣ n₂ - ν := by omega
    have h5 := szh1n_pow_five (h25₂ u₂ hu₂) f₂ h25'
    left
    rw [hcm.mul_pow, h5, mul_one]
    exact P₁.pow_mem hu₁ 5
  · have h5 := szh1n_pow_five (h25₁ u₁ hu₁) f₁ h25
    right
    rw [hcm.mul_pow, h5, one_mul]
    exact P₂.pow_mem hu₂ 5

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
