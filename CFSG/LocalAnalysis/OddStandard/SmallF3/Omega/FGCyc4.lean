module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem fg_card_le_two_of_le_zpowers {Γ : Type*} [Group Γ] {γ : Γ} (hγ : γ ^ 2 = 1)
    {A : Subgroup Γ} (hA : A ≤ Subgroup.zpowers γ) : Nat.card A ≤ 2 := by
  haveI : Finite (Subgroup.zpowers γ) :=
    finite_zpowers.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by norm_num, hγ⟩)
  have h1 : Nat.card A ≤ Nat.card (Subgroup.zpowers γ) := Subgroup.card_le_of_le hA
  rw [Nat.card_zpowers] at h1
  exact h1.trans (orderOf_le_of_pow_eq_one (by norm_num) hγ)

theorem fg_card_le_two_or_cyclic_four {Γ : Type*} [Group Γ] {γ : Γ} (hγ : γ ^ 4 = 1)
    {A : Subgroup Γ} (hA : A ≤ Subgroup.zpowers γ) :
    Nat.card A ≤ 2 ∨ Nonempty (↥A ≃* Multiplicative (ZMod 4)) := by
  haveI : Finite (Subgroup.zpowers γ) :=
    finite_zpowers.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨4, by norm_num, hγ⟩)
  have hdvd4 : Nat.card A ∣ 4 := by
    have h1 : Nat.card A ∣ Nat.card (Subgroup.zpowers γ) := Subgroup.card_dvd_of_le hA
    rw [Nat.card_zpowers] at h1
    exact h1.trans (orderOf_dvd_of_pow_eq_one hγ)
  by_cases hle : Nat.card A ≤ 2
  · exact Or.inl hle
  · right
    have hge : 3 ≤ Nat.card A := by omega
    have hle4 : Nat.card A ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd4
    have hcard : Nat.card A = 4 := by
      have hcases : Nat.card A = 3 ∨ Nat.card A = 4 := by omega
      rcases hcases with h | h
      · rw [h] at hdvd4
        exact absurd hdvd4 (by decide)
      · exact h
    haveI : IsCyclic ↥A := Subgroup.isCyclic_of_le hA
    have e := (zmodCyclicMulEquiv (G := ↥A) inferInstance).symm
    generalize hn : Nat.card ↥A = n at e hcard
    subst hcard
    exact ⟨e⟩

end CFSG.OddStandard.SmallF3.Omega
