module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatC5PSLBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinField
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinInner

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat.C5PSL

open CFSG Subgroup CFSG.Open CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.CatLeafProof.X10Lin
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (innerDiagonalAction)
open CFSG.ComponentClassification.CatalogueBLinearSemilinear (semilinearAction)
open CFSG.ComponentClassification.CatalogueBGraphField (graphFieldAction)
open scoped MatrixGroups

theorem a5Shape_inner {n f : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = 5 ^ f)
    (hadm : StatedLieAdmissible .PSL n 5 f) (A : GL (Fin n) K)
    (hA : orderOf (innerDiagonalAction n K A) = 2) :
    A5Shape n f (fixedSubgroup (innerDiagonalAction n K A)) := by
  intro L hL hA5 hz _
  exfalso
  rcases inner_psl_component_cases Nat.prime_five (by norm_num : (5 : ℕ) ≠ 2) hK hadm A hA hL with
    ⟨z, hzL, hzc, hzz, hz1⟩ | ⟨t, m, e, hT, hadm', hm'⟩
  · exact hz1 (hz z hzL hzc hzz)
  · obtain ⟨rfl, rfl, rfl⟩ := eq_psl_two_one_of_a5 (Or.inl (tag_of_mem_linInnerTuples hT)) hadm'
      hm' hA5
    exact not_mem_linInnerTuples hT

theorem a5Shape_field {n f : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 5 ^ f) (hf : 1 ≤ f) (A : GL (Fin n) K) (τ : K ≃+* K) (hτ : τ ≠ 1)
    (hsq : semilinearAction n K A τ ^ 2 = 1) :
    A5Shape n f (fixedSubgroup (semilinearAction n K A τ)) := by
  intro L hL hA5 _ _
  obtain ⟨j, hj, hadm', hm'⟩ := field_psl_component_model hn Nat.prime_five
    (by norm_num : (5 : ℕ) ≠ 2) hf hK A τ hτ hsq (MulEquiv.refl _) hL
  obtain ⟨-, rfl, rfl⟩ := eq_psl_two_one_of_a5 (Or.inl rfl) hadm' hm' hA5
  exact Or.inl ⟨rfl, by omega⟩

theorem a5Shape_graphField {n f : ℕ} (hn : 3 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 5 ^ f) (hf : 1 ≤ f) (A : GL (Fin n) K) (τ : K ≃+* K) (hτ : τ ≠ 1)
    (hord : orderOf (graphFieldAction n K A τ) = 2) :
    A5Shape n f (fixedSubgroup (graphFieldAction n K A τ)) := by
  intro L hL hA5 _ _
  exfalso
  obtain ⟨j, hj, hadm', hm'⟩ := graphField_psl_component_model hn Nat.prime_five
    (by norm_num : (5 : ℕ) ≠ 2) hf hK A τ hτ hord (MulEquiv.refl _) hL
  obtain ⟨h, -⟩ := eq_psl_two_one_of_a5 (Or.inr (Or.inl rfl)) hadm' hm' hA5
  exact absurd h (by decide)

end CFSG.ComponentClassification.SolMax.FiveCat.C5PSL
