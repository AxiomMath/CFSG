module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootStd

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Polynomial

section Field

theorem pow_pow_card_sq' {K : Type} [Field K] [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2)
    (c : K) : (c ^ q) ^ q = c := by
  have := Fintype.ofFinite K
  rw [← pow_mul, ← sq, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]

theorem exists_pow_ne {K : Type} [Field K] [Finite K] {q : ℕ} (hq : 2 ≤ q)
    (hK : Nat.card K = q ^ 2) : ∃ c : K, c ^ q ≠ c := by
  by_contra h
  push Not at h
  have := Fintype.ofFinite K
  have hq1 : 1 < q := hq
  have hne := FiniteField.X_pow_card_sub_X_ne_zero K hq1
  have hdeg := FiniteField.X_pow_card_sub_X_natDegree_eq K hq1
  have hsub : (Finset.univ : Finset K).val ⊆ (X ^ q - X : K[X]).roots := by
    intro c _
    rw [mem_roots hne]
    simp [h c]
  have := Polynomial.card_le_degree_of_subset_roots hsub
  rw [hdeg, Finset.card_univ, ← Nat.card_eq_fintype_card, hK] at this
  nlinarith

theorem two_le_of_card_sq {K : Type} [Field K] [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2) :
    2 ≤ q := by
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  rw [hK] at h1
  by_contra h
  push Not at h
  interval_cases q <;> simp at h1

theorem card_orbit_zero : (TwistTag.E6.orbit 0).card = 2 := by decide
theorem card_orbit_one : (TwistTag.E6.orbit 1).card = 2 := by decide
theorem card_orbit_two : (TwistTag.E6.orbit 2).card = 1 := by decide
theorem card_orbit_a2 : (TwistTag.E6.orbit a2).card = 1 := by decide

variable {K : Type} [Field K]

theorem mem_orbitField_of_card_eq_one (σ : K →+* K) {a : Fin TwistTag.E6.foldedTag.rank}
    (h : (TwistTag.E6.orbit a).card = 1) (c : K) :
    c ∈ orbitField TwistTag.E6 K σ a ↔ σ c = c := by
  rw [mem_orbitField, h, pow_one]

theorem mem_orbitField_of_card_eq_two (σ : K →+* K) (hσσ : ∀ c, σ (σ c) = c)
    {a : Fin TwistTag.E6.foldedTag.rank} (h : (TwistTag.E6.orbit a).card = 2) (c : K) :
    c ∈ orbitField TwistTag.E6 K σ a := by
  rw [mem_orbitField, h, pow_two]
  exact hσσ c

end Field

end CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot
