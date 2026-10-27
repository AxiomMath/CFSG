module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSLField
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddPSL

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Matrix
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)
open CFSG.ComponentClassification.CatLeafProof (GLS3OddFamilyInput nonempty_mulEquiv_psl_of_lieModel
  psl_two_normal_form)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatalogueBLinearSemilinear (semilinearAction)
open CFSG.ComponentClassification.CatalogueBGraphForm (pureGraphAction)
open CFSG.ComponentClassification.CatalogueBGraphField (graphFieldAction)

theorem PSLA6.a6Shape_PSL_iff {n f : ℕ} :
    A6Shape .PSL n f ↔ (n = 2 ∧ f = 4) ∨ (n = 3 ∧ f = 2) ∨ (n = 4 ∧ f = 1) := by
  simp [A6Shape]

open PSLA6

section Concrete

variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem a6_psl_concrete (hO : LieOrderFormulasInput) (hgraph : ∀ (_ : LieOrderFormulasInput) {n f :
    ℕ} {K : Type} [Field K] [Finite K], Nat.card K = 3 ^ f → 3 ≤ n → StatedLieAdmissible .PSL n 3 f
    → LieModel (ProjectiveSpecialLinearGroup (Fin n) K) .PSL n 3 f → ∀ A : GL (Fin n) K, orderOf
    (pureGraphAction n K A) = 2 → ∀ D : Subgroup ↥(fixedSubgroup (pureGraphAction n K A)), A6Hyp
    (pureGraphAction n K A) D → A6Shape .PSL n f)
    (hgf : ∀ (_ : LieOrderFormulasInput) {n f : ℕ} {K : Type} [Field K] [Finite K], Nat.card K = 3 ^
        f → 3 ≤ n → StatedLieAdmissible .PSL n 3 f → LieModel (ProjectiveSpecialLinearGroup (Fin n)
        K) .PSL n 3 f → ∀ (A : GL (Fin n) K) (σ : K ≃+* K), σ ≠ 1 → orderOf (graphFieldAction n K A
        σ) = 2 → ∀ D : Subgroup ↥(fixedSubgroup (graphFieldAction n K A σ)), A6Hyp (graphFieldAction
        n K A σ) D → False) {f : ℕ} (hK : Nat.card K = 3 ^ f)
    (hadm : StatedLieAdmissible .PSL n 3 f)
    (hm : LieModel (ProjectiveSpecialLinearGroup (Fin n) K) .PSL n 3 f)
    (σ : MulAut (ProjectiveSpecialLinearGroup (Fin n) K)) (hσ : orderOf σ = 2)
    {D : Subgroup ↥(fixedSubgroup σ)} (hD : A6Hyp σ D) : A6Shape .PSL n f := by
  rw [a6Shape_PSL_iff]
  have hn : 2 ≤ n := hadm.2.2.1
  have hsemi : ∀ (A : GL (Fin n) K) (τ : K ≃+* K), σ = semilinearAction n K A τ →
      (n = 2 ∧ f = 4) ∨ (n = 4 ∧ f = 1) := by
    intro A τ hAτ
    by_cases hτ : τ = 1
    · subst hτ
      rw [CatalogueBLinearSemilinear.semilinearAction_one_field] at hAτ
      subst hAτ
      exact Or.inr (a6_psl_inner hO hK hadm hm A hσ hD)
    · subst hAτ
      exact Or.inl (a6_psl_field hO hK hadm hm A τ hτ hσ hD)
  rcases (by omega : n = 2 ∨ 3 ≤ n) with rfl | hn3
  · obtain ⟨A, τ, hAτ⟩ := psl_two_normal_form σ
    rcases hsemi A τ hAτ with h | h
    · exact Or.inl h
    · exact absurd h.1 (by omega)
  · obtain ⟨-, hgen⟩ := LocalAnalysis.ComponentInitial.LinearFlag.automorphism_generation
      (K := K) hn3
    obtain ⟨A, τ, ε, hε, hAσε⟩ :=
      hgen (MulAut.congr (CatalogueBLinearHigherB.nativeEquiv n K).symm σ)
    have hβ' : σ = MulAut.congr (CatalogueBLinearHigherB.nativeEquiv n K)
        (LocalAnalysis.ComponentInitial.LinearFlag.conjAut n K A *
          LocalAnalysis.ComponentInitial.LinearFlag.fieldAut n K τ *
            LocalAnalysis.ComponentInitial.LinearFlag.dualAut n K ^ ε) := by
      rw [← hAσε]
      ext x
      simp
    interval_cases ε
    · rw [pow_zero, mul_one, CatalogueBLinearHigherB.congr_semilinear] at hβ'
      rcases hsemi A τ hβ' with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rw [pow_one] at hβ'
      by_cases hτ : τ = 1
      · subst hτ
        rw [map_one, mul_one, CatalogueBLinearHigherB.congr_pureGraph] at hβ'
        subst hβ'
        exact (a6Shape_PSL_iff).mp (hgraph hO hK hn3 hadm hm A hσ D hD)
      · rw [CatalogueBLinearHigherB.congr_graphField] at hβ'
        subst hβ'
        exact (hgf hO hK hn3 hadm hm A τ hτ hσ D hD).elim

end Concrete

theorem oddA6Shape_PSL_of_graph (hO : LieOrderFormulasInput)
    (hgls : GLS3OddFamilyInput .PSL) (hgraph : ∀ (_ : LieOrderFormulasInput) {n f : ℕ} {K : Type}
        [Field K] [Finite K], Nat.card K = 3 ^ f → 3 ≤ n → StatedLieAdmissible .PSL n 3 f → LieModel
        (ProjectiveSpecialLinearGroup (Fin n) K) .PSL n 3 f → ∀ A : GL (Fin n) K, orderOf
        (pureGraphAction n K A) = 2 → ∀ D : Subgroup ↥(fixedSubgroup (pureGraphAction n K A)), A6Hyp
        (pureGraphAction n K A) D → A6Shape .PSL n f) (hgf : ∀ (_ :
        LieOrderFormulasInput) {n f : ℕ} {K : Type} [Field K] [Finite K], Nat.card K = 3 ^ f → 3 ≤ n
        → StatedLieAdmissible .PSL n 3 f → LieModel (ProjectiveSpecialLinearGroup (Fin n) K) .PSL n
        3 f → ∀ (A : GL (Fin n) K) (σ : K ≃+* K), σ ≠ 1 → orderOf (graphFieldAction n K A σ) = 2 → ∀
        D : Subgroup ↥(fixedSubgroup (graphFieldAction n K A σ)), A6Hyp (graphFieldAction n K A σ) D
        → False) :
    OddA6Shape .PSL := by
  apply oddA6Shape_of_concrete
  intro S _ _ n p f hp hp2 hadm hm
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_psl_of_lieModel hadm hm
  refine ⟨ProjectiveSpecialLinearGroup (Fin n) K, inferInstance, inferInstance, e, ?_⟩
  intro σ D hσ hD
  have hmX : LieModel (ProjectiveSpecialLinearGroup (Fin n) K) .PSL n p f :=
    Blueprint.LieModel.of_mulEquiv e hm
  have hp3 : p = 3 := hD.char_three hO hgls hp hp2 hadm hmX hσ
  subst hp3
  exact ⟨rfl, a6_psl_concrete hO hgraph hgf hK hadm hmX σ hσ hD, fun h => by cases h⟩

end CFSG.ComponentClassification.CatFC
