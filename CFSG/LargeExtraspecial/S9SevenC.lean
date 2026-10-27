module

public import CFSG.LargeExtraspecial.S9TwoA

public section

namespace CFSG.LargeExtraspecial.S9

open Subgroup

section Dihedral

variable {Y : Type*} [Group Y]

theorem conj_zpow_mul_pair {s s' : Y} (hs : s * s = 1) (hs' : s' * s' = 1) (j : ℤ) :
    s * (s * s') ^ j * s⁻¹ = ((s * s') ^ j)⁻¹ := by
  have h1 : s * (s * s') * s⁻¹ = (s * s')⁻¹ := by
    have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
    have hs'i : s'⁻¹ = s' := inv_eq_of_mul_eq_one_right hs'
    rw [mul_inv_rev, hsi, hs'i, ← mul_assoc, hs, one_mul]
  have h2 : (MulAut.conj s) ((s * s') ^ j) = ((MulAut.conj s) (s * s')) ^ j := map_zpow _ _ _
  simp only [MulAut.conj_apply] at h2
  rw [h2, h1, inv_zpow]

theorem exists_zpow_of_mem_closure_pair {s s' : Y} (hs : s * s = 1) (hs' : s' * s' = 1)
    {c : Y} (hc : c ∈ closure ({s, s'} : Set Y)) :
    ∃ j : ℤ, c = (s * s') ^ j ∨ c = (s * s') ^ j * s := by
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hconj : ∀ j : ℤ, s * (s * s') ^ j * s = (s * s') ^ (-j) := by
    intro j
    have := conj_zpow_mul_pair hs hs' j
    rwa [hsi, ← zpow_neg] at this
  let D : Subgroup Y :=
    { carrier := {x | ∃ j : ℤ, x = (s * s') ^ j ∨ x = (s * s') ^ j * s}
      mul_mem' := by
        rintro x y ⟨i, rfl | rfl⟩ ⟨j, rfl | rfl⟩
        · exact ⟨i + j, Or.inl (zpow_add _ _ _).symm⟩
        · exact ⟨i + j, Or.inr (by rw [← mul_assoc, ← zpow_add])⟩
        · refine ⟨i - j, Or.inr ?_⟩
          calc (s * s') ^ i * s * (s * s') ^ j
              = (s * s') ^ i * s * (s * s') ^ j * (s * s) := by rw [hs, mul_one]
            _ = (s * s') ^ i * (s * (s * s') ^ j * s) * s := by group
            _ = (s * s') ^ (i - j) * s := by rw [hconj, ← zpow_add, sub_eq_add_neg]
        · refine ⟨i - j, Or.inl ?_⟩
          calc (s * s') ^ i * s * ((s * s') ^ j * s)
              = (s * s') ^ i * (s * (s * s') ^ j * s) := by group
            _ = (s * s') ^ (i - j) := by rw [hconj, ← zpow_add, sub_eq_add_neg]
      one_mem' := ⟨0, Or.inl (zpow_zero _).symm⟩
      inv_mem' := by
        rintro x ⟨j, rfl | rfl⟩
        · exact ⟨-j, Or.inl (zpow_neg _ _).symm⟩
        · refine ⟨j, Or.inr ?_⟩
          calc ((s * s') ^ j * s)⁻¹ = s * (s * s') ^ (-j) := by rw [mul_inv_rev, hsi, zpow_neg]
            _ = (s * (s * s') ^ (-j) * s) * s := by rw [mul_assoc _ s s, hs, mul_one]
            _ = (s * s') ^ j * s := by rw [hconj, neg_neg] }
  have hle : closure ({s, s'} : Set Y) ≤ D := by
    rw [closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨⟨0, Or.inr (by rw [zpow_zero, one_mul])⟩, ⟨-1, Or.inr ?_⟩⟩
    rw [zpow_neg, zpow_one, mul_inv_rev, hsi, inv_eq_of_mul_eq_one_right hs', mul_assoc, hs,
      mul_one]
  exact hle hc

theorem sq_eq_one_of_commute_of_mem_closure_pair {s s' : Y} (hs : s * s = 1)
    (hs' : s' * s' = 1) {c : Y} (hc : c ∈ closure ({s, s'} : Set Y)) (hcs : c * s = s * c) :
    c * c = 1 := by
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  obtain ⟨j, rfl | rfl⟩ := exists_zpow_of_mem_closure_pair hs hs' hc
  · have h1 := conj_zpow_mul_pair hs hs' j
    have h2 : s * (s * s') ^ j * s⁻¹ = (s * s') ^ j := by
      rw [← hcs, mul_assoc, mul_inv_cancel, mul_one]
    rw [h2] at h1
    calc (s * s') ^ j * (s * s') ^ j = (s * s') ^ j * ((s * s') ^ j)⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel _
  · have h1 := conj_zpow_mul_pair hs hs' j
    rw [hsi] at h1
    calc (s * s') ^ j * s * ((s * s') ^ j * s) = (s * s') ^ j * (s * (s * s') ^ j * s) := by
          group
      _ = 1 := by rw [h1, mul_inv_cancel]

end Dihedral

theorem perm_three_mem_words : ∀ σ τ π : Equiv.Perm (Fin 3), σ * τ ≠ τ * σ →
    π = 1 ∨ π = σ ∨ π = τ ∨ π = σ * τ ∨ π = τ * σ ∨ π = σ * σ ∨ π = σ * τ * σ := by
  decide

theorem eq_top_of_not_commute {K : Subgroup (Equiv.Perm (Fin 3))} {σ τ : Equiv.Perm (Fin 3)}
    (hσ : σ ∈ K) (hτ : τ ∈ K) (hστ : σ * τ ≠ τ * σ) : K = ⊤ := by
  refine eq_top_iff.mpr fun π _ => ?_
  rcases perm_three_mem_words σ τ π hστ with h | h | h | h | h | h | h <;> rw [h]
  · exact one_mem K
  · exact hσ
  · exact hτ
  · exact mul_mem hσ hτ
  · exact mul_mem hτ hσ
  · exact mul_mem hσ hσ
  · exact mul_mem (mul_mem hσ hτ) hσ

end CFSG.LargeExtraspecial.S9
