module

public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.L4U4

open scoped MatrixGroups

variable {F : Type} [Field F] [Finite F] {G : Type*} [Group G]

omit [Field F] in
theorem exists_finset_card_four (h4 : 4 ≤ Nat.card F) : ∃ s : Finset F, s.card = 4 := by
  have := Fintype.ofFinite F
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4)
  exact ⟨s, hs⟩

noncomputable def rangeEquivPSL (φ : SL(2, F) →* G)
    (hker : φ.ker = Subgroup.center SL(2, F)) :
    φ.range ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
  (QuotientGroup.quotientKerEquivRange φ).symm.trans (QuotientGroup.quotientMulEquivOfEq hker)

theorem isSimpleGroup_range_of_ker_eq_center (h4 : 4 ≤ Nat.card F) (φ : SL(2, F) →* G)
    (hker : φ.ker = Subgroup.center SL(2, F)) : IsSimpleGroup φ.range :=
  have := (CFSG.LinearGroups.linear_projective_simple (K := F) (n := 2) le_rfl
    (Or.inr (exists_finset_card_four h4))).2.1
  (rangeEquivPSL φ hker).isSimpleGroup

theorem isPerfect_range_of_ker_eq_center (h4 : 4 ≤ Nat.card F) (φ : SL(2, F) →* G)
    (hker : φ.ker = Subgroup.center SL(2, F)) : Group.IsPerfect φ.range :=
  have := CFSG.LinearGroups.linear_projective_perfect (K := F) (n := 2) le_rfl
    (Or.inr (exists_finset_card_four h4))
  Group.IsPerfect.ofSurjective (f := (rangeEquivPSL φ hker).symm.toMonoidHom)
    (MulEquiv.surjective _)

theorem le_normalizer_of_forall_conj {C L : Subgroup G}
    (h : ∀ y ∈ C, ∀ x ∈ L, y * x * y⁻¹ ∈ L) : C ≤ Subgroup.normalizer (L : Set G) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h y hy x, fun hx => ?_⟩
  simpa [mul_assoc] using h y⁻¹ (C.inv_mem hy) _ hx

theorem eq_one_or_eq_neg_one_of_mul_eq_smul {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] {K : Type*} [Field K] {A : Matrix n n K} {a : K} (ha : a ≠ 0)
    (hAA : A * A = a • 1) {Y : Matrix.GeneralLinearGroup n K} {c : K}
    (hc : (Y : Matrix n n K) * A = c • (A * (Y : Matrix n n K))) : c = 1 ∨ c = -1 := by
  set Ym := (Y : Matrix n n K)
  have e1 : Ym * (A * A) = c ^ 2 • ((A * A) * Ym) := by
    calc Ym * (A * A) = (Ym * A) * A := (Matrix.mul_assoc _ _ _).symm
      _ = (c • (A * Ym)) * A := by rw [hc]
      _ = c • (A * (Ym * A)) := by rw [Matrix.smul_mul, Matrix.mul_assoc]
      _ = c • (A * (c • (A * Ym))) := by rw [hc]
      _ = c ^ 2 • ((A * A) * Ym) := by
          rw [Matrix.mul_smul, smul_smul, ← Matrix.mul_assoc, sq]
  rw [hAA, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul] at e1
  have e2 : (a - c ^ 2 * a) • Ym = 0 := by rw [sub_smul, e1, sub_self]
  rcases smul_eq_zero.mp e2 with h3 | h3
  · have h4 : (1 - c ^ 2) * a = 0 := by linear_combination h3
    rcases mul_eq_zero.mp h4 with h5 | h5
    · exact mul_self_eq_one_iff.mp (by linear_combination -h5)
    · exact absurd h5 ha
  · exact absurd h3 Y.ne_zero

end CFSG.ClassicalInvolution.Q3.TA3.L4U4
