module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10B123

open Equiv Subgroup

abbrev A5 : Type := ↥(alternatingGroup (Fin 5))

theorem a5_centralizer :
    ∀ c g : A5, c ^ 5 = 1 → c ≠ 1 → g * c = c * g → ∃ k : Fin 5, g = c ^ (k : ℕ) := by
  decide +kernel

theorem a5_center : ∀ z : A5, (∀ g : A5, g * z = z * g) → z = 1 := by
  decide +kernel

theorem a5_exists_ne_one : ∃ g : A5, g ≠ 1 := by
  decide +kernel

theorem a5_pow_four : ∀ g : A5, g ^ 4 = 1 → g ^ 2 = 1 := by
  decide +kernel

theorem a5_conj_noncomm :
    ∀ c h : A5, c ^ 5 = 1 → c ≠ 1 → h ^ 2 = 1 → h ≠ 1 →
      ∃ k j : Fin 5, (c ^ (k : ℕ) * h * (c ^ (k : ℕ))⁻¹) * (c ^ (j : ℕ) * h * (c ^ (j : ℕ))⁻¹) ≠
        (c ^ (j : ℕ) * h * (c ^ (j : ℕ))⁻¹) * (c ^ (k : ℕ) * h * (c ^ (k : ℕ))⁻¹) := by
  decide +kernel

theorem a5_card : Nat.card A5 = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  rfl

theorem a5_two_elem {g : A5} (h : ∃ n : ℕ, g ^ (2 ^ n) = 1) : g ^ 2 = 1 := by
  obtain ⟨n, hn⟩ := h
  have h1 : orderOf g ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
  have h2 : orderOf g ∣ 60 := a5_card ▸ orderOf_dvd_natCard g
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  have hi2 : i ≤ 2 := by
    by_contra hlt
    have h8 : 2 ^ 3 ∣ 2 ^ i := pow_dvd_pow 2 (by omega)
    rw [← hi] at h8
    have := h8.trans h2
    omega
  have h4 : orderOf g ∣ 4 := by
    rw [hi]
    exact (pow_dvd_pow 2 hi2 : 2 ^ i ∣ 2 ^ 2)
  exact a5_pow_four g (orderOf_dvd_iff_pow_eq_one.1 h4)

theorem a5_two_subgroup {c : A5} (hc5 : c ^ 5 = 1) (hc1 : c ≠ 1) {H : Subgroup A5}
    (hH : IsPGroup 2 H) (hn : ∀ h ∈ H, c * h * c⁻¹ ∈ H) : H = ⊥ := by
  rw [eq_bot_iff]
  intro h hh
  by_contra hne
  have hne1 : h ≠ 1 := fun e => hne (by rw [e]; exact one_mem _)
  have hsq : ∀ g ∈ H, g ^ 2 = 1 := by
    intro g hg
    apply a5_two_elem
    obtain ⟨n, hn⟩ := hH ⟨g, hg⟩
    exact ⟨n, congrArg Subtype.val hn⟩
  have hconj : ∀ k : ℕ, c ^ k * h * (c ^ k)⁻¹ ∈ H := by
    intro k
    induction k with
    | zero => simpa using hh
    | succ k ih =>
      have := hn _ ih
      have e : c * (c ^ k * h * (c ^ k)⁻¹) * c⁻¹ = c ^ (k + 1) * h * (c ^ (k + 1))⁻¹ := by
        rw [pow_succ', mul_inv_rev]
        group
      rwa [e] at this
  obtain ⟨k, j, hkj⟩ := a5_conj_noncomm c h hc5 hc1 (hsq h hh) hne1
  apply hkj
  have hx := hsq _ (hconj k)
  have hy := hsq _ (hconj j)
  have hxy := hsq _ (H.mul_mem (hconj k) (hconj j))
  generalize c ^ (k : ℕ) * h * (c ^ (k : ℕ))⁻¹ = x at hx hxy ⊢
  generalize c ^ (j : ℕ) * h * (c ^ (j : ℕ))⁻¹ = y at hy hxy ⊢
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hx)
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hy)
  have hxy' : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hxy)
  rw [mul_inv_rev, hx', hy'] at hxy'
  exact hxy'.symm

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10B123
