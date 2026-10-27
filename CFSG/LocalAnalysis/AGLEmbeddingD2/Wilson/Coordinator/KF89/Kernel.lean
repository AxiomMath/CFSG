module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.Index
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF89

variable {J Q₁ Q₂ : Type*} [Group J] [Group Q₁] [Group Q₂]

theorem ker_eq_of_simple [Finite J] (f₁ : J →* Q₁) (f₂ : J →* Q₂)
    (hS : IsSimpleGroup f₁.range) (hns : ¬ Group.IsSolvable f₁.range)
    (hsol : Group.IsSolvable f₂.ker)
    (h360 : Nat.card f₁.range = 360) (h3 : ¬ 3 ∣ Nat.card f₁.ker)
    (hdvd : Nat.card f₂.range ∣ 1080 ∨ Nat.card f₂.range ∣ 243) : f₁.ker = f₂.ker := by
  have hle : f₂.ker ≤ f₁.ker := by
    set φ : J →* f₁.range := f₁.rangeRestrict with hφ
    have hφs : Function.Surjective φ := f₁.rangeRestrict_surjective
    set N : Subgroup f₁.range := f₂.ker.map φ with hN
    have hNn : N.Normal := (f₂.normal_ker).map φ hφs
    have hNs : Group.IsSolvable N :=
      Group.isSolvable_of_surjective (φ.subgroupMap_surjective f₂.ker)
    have := hS
    have := hNn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · intro j hj
      have hφj : φ j ∈ N := ⟨j, hj, rfl⟩
      rw [h, Subgroup.mem_bot] at hφj
      rw [MonoidHom.mem_ker]
      have := congrArg Subtype.val hφj
      simpa [hφ] using this
    · exfalso
      apply hns
      rw [h] at hNs
      exact Group.isSolvable_of_surjective
        (f := (Subgroup.topEquiv : (⊤ : Subgroup f₁.range) ≃* _).toMonoidHom)
        (MulEquiv.surjective _)
  have hc₁ : Nat.card f₁.ker * Nat.card f₁.range = Nat.card J := by
    rw [← Subgroup.index_ker]; exact Subgroup.card_mul_index _
  have hc₂ : Nat.card f₂.ker * Nat.card f₂.range = Nat.card J := by
    rw [← Subgroup.index_ker]; exact Subgroup.card_mul_index _
  obtain ⟨i, hi⟩ := Subgroup.card_dvd_of_le hle
  have hpos : 0 < Nat.card f₂.ker := Nat.card_pos
  have hr : Nat.card f₂.range = 360 * i := by
    have : Nat.card f₂.ker * Nat.card f₂.range = Nat.card f₂.ker * (360 * i) := by
      rw [hc₂, ← hc₁, hi, h360]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have hi3 : i ∣ 3 := by
    rw [hr] at hdvd
    rcases hdvd with hdvd | hdvd
    · have : 360 * i ∣ 360 * 3 := by simpa using hdvd
      exact (Nat.mul_dvd_mul_iff_left (by norm_num)).mp this
    · exfalso
      have h360 : 360 ∣ 243 := (Dvd.intro i rfl).trans hdvd
      norm_num at h360
  have hi1 : i = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hi3 with h | h
    · exact h
    · exfalso
      apply h3
      rw [hi, h]
      exact Dvd.intro_left _ rfl
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hi, hi1, mul_one]

section Transfer

variable (f₁ : J →* Q₁) (f₂ : J →* Q₂) (hker : f₁.ker = f₂.ker)
include hker

theorem eq_of_eq_of_ker_eq {j j' : J} (h : f₁ j = f₁ j') : f₂ j = f₂ j' := by
  have h1 : j * j'⁻¹ ∈ f₁.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
  rw [hker, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at h1
  exact h1

theorem eq_of_eq_of_ker_eq' {j j' : J} (h : f₂ j = f₂ j') : f₁ j = f₁ j' :=
  eq_of_eq_of_ker_eq f₂ f₁ hker.symm h

variable {f₁ f₂} {α : J → J} {σ₁ : Q₁ → Q₁} {σ₂ : Q₂ → Q₂}
  (h₁ : ∀ j, f₁ (α j) = σ₁ (f₁ j)) (h₂ : ∀ j, f₂ (α j) = σ₂ (f₂ j))
include h₁ h₂

theorem transfer_involution (hσ : ∀ x ∈ f₁.range, σ₁ (σ₁ x) = x) :
    ∀ k ∈ f₂.range, σ₂ (σ₂ k) = k := by
  rintro _ ⟨j, rfl⟩
  have h : f₁ (α (α j)) = f₁ j := by
    rw [h₁, h₁]
    exact hσ _ ⟨j, rfl⟩
  have h' := eq_of_eq_of_ker_eq f₁ f₂ hker h
  rwa [h₂, h₂] at h'

theorem transfer_outer (hσ : ∀ g ∈ f₁.range, ∃ x ∈ f₁.range, σ₁ x ≠ g * x * g⁻¹) :
    ∀ g ∈ f₂.range, ∃ k ∈ f₂.range, σ₂ k ≠ g * k * g⁻¹ := by
  rintro _ ⟨j₀, rfl⟩
  obtain ⟨_, ⟨j, rfl⟩, hne⟩ := hσ (f₁ j₀) ⟨j₀, rfl⟩
  refine ⟨f₂ j, ⟨j, rfl⟩, fun heq => hne ?_⟩
  have h : f₂ (α j) = f₂ (j₀ * j * j₀⁻¹) := by
    rw [h₂, heq, map_mul, map_mul, map_inv]
  have h' := eq_of_eq_of_ker_eq' f₁ f₂ hker h
  rw [h₁, map_mul, map_mul, map_inv] at h'
  exact h'

theorem transfer_fixed (hw : ∃ w ∈ f₁.range, w ^ 3 = 1 ∧ w ≠ 1 ∧ σ₁ w = w) :
    ∃ w ∈ f₂.range, w ^ 3 = 1 ∧ w ≠ 1 ∧ σ₂ w = w := by
  obtain ⟨_, ⟨j, rfl⟩, hw3, hw1, hwσ⟩ := hw
  refine ⟨f₂ j, ⟨j, rfl⟩, ?_, ?_, ?_⟩
  · have h : f₁ (j ^ 3) = f₁ 1 := by rw [map_pow, hw3, map_one]
    have h' := eq_of_eq_of_ker_eq f₁ f₂ hker h
    rwa [map_pow, map_one] at h'
  · intro h1
    apply hw1
    have h : f₂ j = f₂ 1 := by rw [h1, map_one]
    have h' := eq_of_eq_of_ker_eq' f₁ f₂ hker h
    rwa [map_one] at h'
  · have h : f₁ (α j) = f₁ j := by rw [h₁, hwσ]
    have h' := eq_of_eq_of_ker_eq f₁ f₂ hker h
    rwa [h₂] at h'

omit h₁ h₂ in
theorem transfer_center (hZ : ∀ x ∈ f₁.range, (∀ z ∈ f₁.range, x * z = z * x) → x = 1) :
    ∀ k ∈ f₂.range, (∀ z ∈ f₂.range, k * z = z * k) → k = 1 := by
  rintro _ ⟨j, rfl⟩ hc
  have h1 : f₁ j = 1 := by
    refine hZ _ ⟨j, rfl⟩ ?_
    rintro _ ⟨j', rfl⟩
    have h : f₂ (j * j') = f₂ (j' * j) := by
      rw [map_mul, map_mul]
      exact hc _ ⟨j', rfl⟩
    have h' := eq_of_eq_of_ker_eq' f₁ f₂ hker h
    rwa [map_mul, map_mul] at h'
  have h : f₁ j = f₁ 1 := by rw [h1, map_one]
  have h' := eq_of_eq_of_ker_eq f₁ f₂ hker h
  rwa [map_one] at h'

omit h₁ h₂ in
theorem card_range_eq : Nat.card f₁.range = Nat.card f₂.range := by
  rw [← Subgroup.index_ker, ← Subgroup.index_ker, hker]

end Transfer

end CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF89
