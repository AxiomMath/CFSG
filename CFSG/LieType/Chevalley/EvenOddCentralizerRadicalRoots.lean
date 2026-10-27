module

public import CFSG.LieType.Chevalley.RootCommutator

public noncomputable section

namespace CFSG.LieType.Chevalley.EvenOddRadical

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement

variable {τ : Tag}

theorem symmetrizer_apply_self (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (j : Fin τ.rank) :
    τ.symmetrizer j j = 1 := by
  rcases hτ with rfl | rfl | rfl | rfl <;> exact Matrix.one_apply_eq j

theorem iform_self_eq_two
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    iform α α = 2 := by
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hα
  rw [hj, symmetrizer_apply_self hτ j, mul_one]

theorem iform_add_smul_single
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (α : Fin τ.rank → ℤ) (i : Fin τ.rank) (m : ℤ) :
    iform (α + m • Pi.single i 1) (α + m • Pi.single i 1) =
      iform α α + 2 * m * iform α (Pi.single i 1) + 2 * m ^ 2 := by
  simp only [iform_add_left, iform_add_right, iform_smul_left, iform_smul_right,
    iform_single_single, symmetrizer_apply_self hτ i]
  rw [iform_comm (Pi.single i 1) α]
  ring

theorem mul_add_eq_zero_of_isRoot
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (i : Fin τ.rank) {m : ℤ} (h : IsRoot τ (α + m • Pi.single i 1)) :
    m * (m + iform α (Pi.single i 1)) = 0 := by
  have h1 := iform_self_eq_two hτ h
  rw [iform_add_smul_single hτ, iform_self_eq_two hτ hα] at h1
  have h2 : 2 * (m * (m + iform α (Pi.single i 1))) = 0 := by linear_combination h1
  exact (mul_eq_zero.1 h2).resolve_left two_ne_zero

theorem string_le_one
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    {i : Fin τ.rank} (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) :
    stringUp τ i α + stringDown τ i α ≤ 1 := by
  obtain ⟨-, hs⟩ := isRoot_add_smul_single_iff hα i h₁ h₂
  by_contra hlt
  rw [not_le] at hlt
  rcases Nat.lt_or_ge 0 (stringUp τ i α) with hp | hp
  ·
    have hr1 := mul_add_eq_zero_of_isRoot hτ hα i ((hs 1).2 ⟨by omega, by omega⟩)
    rcases Nat.lt_or_ge 1 (stringUp τ i α) with hp2 | hp2
    · have hr2 := mul_add_eq_zero_of_isRoot hτ hα i ((hs 2).2 ⟨by omega, by omega⟩)
      omega
    · have hr3 := mul_add_eq_zero_of_isRoot hτ hα i ((hs (-1)).2 ⟨by omega, by omega⟩)
      omega
  ·
    have hr1 := mul_add_eq_zero_of_isRoot hτ hα i ((hs (-1)).2 ⟨by omega, by omega⟩)
    have hr2 := mul_add_eq_zero_of_isRoot hτ hα i ((hs (-2)).2 ⟨by omega, by omega⟩)
    omega

section Operators

variable {R : Type*} [CommRing R]

theorem rootVec_of_isRoot {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    rootVec τ R β = Finsupp.single (Sum.inr ⟨β, hβ⟩) 1 := by
  rw [rootVec, dite_eq_left hβ]

theorem rootVec_of_not {β : Fin τ.rank → ℤ} (hβ : ¬IsRoot τ β) : rootVec τ R β = 0 := by
  rw [rootVec, dite_eq_right hβ]

theorem xOp_rootVec
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (i : Fin τ.rank) (c : R)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (h₁ : α ≠ Pi.single i 1)
    (h₂ : α ≠ -Pi.single i 1) :
    xOp τ R i c (rootVec τ R α) = rootVec τ R α + c • rootVec τ R (α + Pi.single i 1) := by
  have hpq := string_le_one hτ hα h₁ h₂
  rw [rootVec_of_isRoot hα, xOp, Finsupp.linearCombination_single, one_smul]
  simp only [ite_eq_right h₁, ite_eq_right h₂]
  rw [← rootVec_of_isRoot hα]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (show stringUp τ i α ≤ 1 by omega) with h0 | h1
  · rw [h0, Finset.sum_range_one]
    have hnot : ¬IsRoot τ (α + Pi.single i 1) := by
      intro h
      obtain ⟨-, hs⟩ := isRoot_add_smul_single_iff hα i h₁ h₂
      have := (hs 1).1 (by rwa [one_smul])
      omega
    simp [rootVec_of_not hnot]
  · have hq : stringDown τ i α = 0 := by omega
    rw [h1, Finset.sum_range_succ, Finset.sum_range_one, hq]
    simp

theorem yOp_rootVec
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (i : Fin τ.rank) (c : R)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (h₁ : α ≠ Pi.single i 1)
    (h₂ : α ≠ -Pi.single i 1) :
    yOp τ R i c (rootVec τ R α) = rootVec τ R α + c • rootVec τ R (α - Pi.single i 1) := by
  have hpq := string_le_one hτ hα h₁ h₂
  rw [rootVec_of_isRoot hα, yOp, Finsupp.linearCombination_single, one_smul]
  simp only [ite_eq_right h₁, ite_eq_right h₂]
  rw [← rootVec_of_isRoot hα]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (show stringDown τ i α ≤ 1 by omega) with h0 | h1
  · rw [h0, Finset.sum_range_one]
    have hnot : ¬IsRoot τ (α - Pi.single i 1) := by
      intro h
      obtain ⟨-, hs⟩ := isRoot_add_smul_single_iff hα i h₁ h₂
      have := (hs (-1)).1 (by rwa [neg_smul, one_smul, ← sub_eq_add_neg])
      omega
    simp [rootVec_of_not hnot]
  · have hp : stringUp τ i α = 0 := by omega
    rw [h1, Finset.sum_range_succ, Finset.sum_range_one, hp]
    simp

end Operators

section Commutator

variable {R : Type} [CommRing R]

theorem pinnedX_conj_of_isRoot
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (h2 : (2 : R) = 0)
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β) (hne : α ≠ β) (hne' : α ≠ -β)
    (h : IsRoot τ (α + β)) (c d : R) :
    pinnedX τ R α c * pinnedX τ R β d * (pinnedX τ R α c)⁻¹ =
      pinnedX τ R (α + β) (c * d) * pinnedX τ R β d := by
  obtain ⟨hI, -⟩ := simply_laced_root_commutator_unit.{0} τ hτ hα hβ hne hne'
  obtain ⟨hε, hF⟩ := hI h
  have hc := hF R c d
  have hε' : (commConst τ α β (1, 1) : R) = 1 := by
    rcases hε with h1 | h1 <;> rw [h1]
    · exact Int.cast_one
    · rw [Int.cast_neg, Int.cast_one]
      exact neg_eq_iff_add_eq_zero.2 (by rw [one_add_one_eq_two, h2])
  rw [hε', one_mul, commutatorElement_def] at hc
  rw [← hc]
  group

theorem pinnedX_conj_of_not
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β) (hne : α ≠ β) (hne' : α ≠ -β)
    (h : ¬IsRoot τ (α + β)) (c d : R) :
    pinnedX τ R α c * pinnedX τ R β d * (pinnedX τ R α c)⁻¹ = pinnedX τ R β d := by
  obtain ⟨-, hF⟩ := simply_laced_root_commutator_unit.{0} τ hτ hα hβ hne hne'
  have hcomm := hF h R (pinnedX τ R α c) (Subgroup.subset_closure ⟨c, rfl⟩) (pinnedX τ R β d)
    (Subgroup.subset_closure ⟨d, rfl⟩)
  rw [hcomm.eq]
  group

end Commutator

end CFSG.LieType.Chevalley.EvenOddRadical
