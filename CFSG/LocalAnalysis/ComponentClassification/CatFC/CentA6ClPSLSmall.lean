module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSLSmallClass
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSLSmallInner4

public noncomputable section

namespace CFSG.ComponentClassification.CatFC.PSLSmall

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Matrix
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)
open CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatalogueBLinearSemilinear (semilinearAction)
open CFSG.ComponentClassification.CatalogueBGraphForm (pureGraphAction)
open CFSG.ComponentClassification.CatalogueBGraphField (graphFieldAction)

@[expose] def PureGraphSmall : Prop :=
  ∀ {n f : ℕ} {K : Type} [Field K] [Finite K], Nat.card K = 3 ^ f → 3 ≤ n → A6Shape .PSL n f →
    ∀ A : GL (Fin n) K, orderOf (pureGraphAction n K A) = 2 →
      ∀ D : Subgroup ↥(fixedSubgroup (pureGraphAction n K A)), A6Hyp (pureGraphAction n K A) D →
        A6SmallConcl .PSL n f (pureGraphAction n K A) D

theorem pureGraphSmall_of_three_four
    (h3 : ∀ {f : ℕ} {K : Type} [Field K] [Finite K], Nat.card K = 3 ^ f → A6Shape .PSL 3 f →
      ∀ A : GL (Fin 3) K, orderOf (pureGraphAction 3 K A) = 2 →
        ∀ D : Subgroup ↥(fixedSubgroup (pureGraphAction 3 K A)), A6Hyp (pureGraphAction 3 K A) D →
          A6SmallConcl .PSL 3 f (pureGraphAction 3 K A) D)
    (h4 : ∀ {f : ℕ} {K : Type} [Field K] [Finite K], Nat.card K = 3 ^ f → A6Shape .PSL 4 f →
      ∀ A : GL (Fin 4) K, orderOf (pureGraphAction 4 K A) = 2 →
        ∀ D : Subgroup ↥(fixedSubgroup (pureGraphAction 4 K A)), A6Hyp (pureGraphAction 4 K A) D →
          A6SmallConcl .PSL 4 f (pureGraphAction 4 K A) D) :
    PureGraphSmall := by
  intro n f K _ _ hK hn hs A hσ D hD
  rcases hs with ⟨-, h, hf⟩ | ⟨-, h, hf⟩ | ⟨-, h, hf⟩ | h | h | h | h | h | h
  · omega
  · subst h
    subst hf
    exact h3 hK (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) A hσ D hD
  · subst h
    subst hf
    exact h4 hK (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))) A hσ D hD
  all_goals exact absurd h.1 (by decide)

section Assembly

variable {K : Type} [Field K] [Finite K]

theorem two_ne_zero_of_odd_card' (hodd : Odd (Nat.card K)) : (2 : K) ≠ 0 :=
  Ring.two_ne_zero (CatalogueBHigherLinearInner.ringChar_ne_two_of_odd_card K hodd)

theorem normal_form_ge_three {n : ℕ} (hn : 3 ≤ n)
    (σ : MulAut (ProjectiveSpecialLinearGroup (Fin n) K)) :
    (∃ (A : GL (Fin n) K) (τ : K ≃+* K), σ = semilinearAction n K A τ) ∨
      (∃ A : GL (Fin n) K, σ = pureGraphAction n K A) ∨
      (∃ (A : GL (Fin n) K) (τ : K ≃+* K), τ ≠ 1 ∧ σ = graphFieldAction n K A τ) := by
  obtain ⟨-, hgen⟩ := LocalAnalysis.ComponentInitial.LinearFlag.automorphism_generation
    (K := K) hn
  obtain ⟨A, τ, ε, hε, hAσε⟩ :=
    hgen (MulAut.congr (CatalogueBLinearHigherB.nativeEquiv n K).symm σ)
  have hσ' : σ = MulAut.congr (CatalogueBLinearHigherB.nativeEquiv n K)
      (LocalAnalysis.ComponentInitial.LinearFlag.conjAut n K A *
        LocalAnalysis.ComponentInitial.LinearFlag.fieldAut n K τ *
          LocalAnalysis.ComponentInitial.LinearFlag.dualAut n K ^ ε) := by
    rw [← hAσε]
    ext x
    simp
  interval_cases ε
  · rw [pow_zero, mul_one, CatalogueBLinearHigherB.congr_semilinear] at hσ'
    exact Or.inl ⟨A, τ, hσ'⟩
  · rw [pow_one] at hσ'
    by_cases hτ : τ = 1
    · subst hτ
      rw [map_one, mul_one, CatalogueBLinearHigherB.congr_pureGraph] at hσ'
      exact Or.inr (Or.inl ⟨A, hσ'⟩)
    · rw [CatalogueBLinearHigherB.congr_graphField] at hσ'
      exact Or.inr (Or.inr ⟨A, τ, hτ, hσ'⟩)

theorem small_inner_two (hK : Nat.card K = 81) {A : GL (Fin 2) K}
    (hσ : orderOf (innerDiagonalAction 2 K A) = 2) :
    SmallStmt .PSL 2 4 (innerDiagonalAction 2 K A) := fun _ hD =>
  (inner_two_false (by rw [hK]; norm_num) (two_ne_zero_of_odd_card' (by rw [hK]; decide)) hσ
    hD).elim

theorem small_inner_three (hK : Nat.card K = 9) {A : GL (Fin 3) K}
    (hσ : orderOf (innerDiagonalAction 3 K A) = 2) :
    SmallStmt .PSL 3 2 (innerDiagonalAction 3 K A) := fun _ hD =>
  (inner_three_false hK (two_ne_zero_of_odd_card' (by rw [hK]; decide)) hσ hD).elim

theorem small_inner_four (hK : Nat.card K = 3) {A : GL (Fin 4) K}
    (hσ : orderOf (innerDiagonalAction 4 K A) = 2) :
    SmallStmt .PSL 4 1 (innerDiagonalAction 4 K A) := fun _ hD =>
  smallConcl_of_big (inner_four_big hK (two_ne_zero_of_odd_card' (by rw [hK]; decide)) hσ hD)

theorem smallStmt_PSL_two (hK : Nat.card K = 81) (σ : MulAut (ProjectiveSpecialLinearGroup (Fin 2) K))
    (hσ : orderOf σ = 2) : SmallStmt .PSL 2 4 σ := by
  by_cases hin : σ ∈ (MulAut.conj : ProjectiveSpecialLinearGroup (Fin 2) K →*
      MulAut (ProjectiveSpecialLinearGroup (Fin 2) K)).range
  · obtain ⟨B, hB⟩ := exists_innerDiagonal_of_mem_range hin
    exact SmallStmt.of_eq hB (small_inner_two hK (hB ▸ hσ))
  · obtain ⟨A, τ, hAτ⟩ := psl_two_normal_form σ
    by_cases hτ : τ = 1
    · have h1 : σ = innerDiagonalAction 2 K A := by
        rw [hAτ, hτ, CatalogueBLinearSemilinear.semilinearAction_one_field]
      exact SmallStmt.of_eq h1 (small_inner_two hK (h1 ▸ hσ))
    · intro D hD
      have hsq0 : σ ^ 2 = 1 := by
        have := pow_orderOf_eq_one σ
        rwa [hσ] at this
      have hsq : semilinearAction 2 K A τ ^ 2 = 1 := by rw [← hAτ]; exact hsq0
      have hev := evidence_semilinear_two hK A hτ hsq
      rw [← hAτ] at hev
      exact smallConcl_of_evidence hD hev (fun h => absurd h hin)

theorem smallStmt_PSL_three (hO : LieOrderFormulasInput) (hgraph : PureGraphSmall)
    (hK : Nat.card K = 9) (σ : MulAut (ProjectiveSpecialLinearGroup (Fin 3) K))
    (hσ : orderOf σ = 2) : SmallStmt .PSL 3 2 σ := by
  by_cases hin : σ ∈ (MulAut.conj : ProjectiveSpecialLinearGroup (Fin 3) K →*
      MulAut (ProjectiveSpecialLinearGroup (Fin 3) K)).range
  · obtain ⟨B, hB⟩ := exists_innerDiagonal_of_mem_range hin
    exact SmallStmt.of_eq hB (small_inner_three hK (hB ▸ hσ))
  · have hsq0 : σ ^ 2 = 1 := by
      have := pow_orderOf_eq_one σ
      rwa [hσ] at this
    rcases normal_form_ge_three (by norm_num : 3 ≤ 3) σ with
      ⟨A, τ, hAτ⟩ | ⟨A, hA⟩ | ⟨A, τ, hτ, hAτ⟩
    · by_cases hτ : τ = 1
      · have h1 : σ = innerDiagonalAction 3 K A := by
          rw [hAτ, hτ, CatalogueBLinearSemilinear.semilinearAction_one_field]
        exact SmallStmt.of_eq h1 (small_inner_three hK (h1 ▸ hσ))
      · have hsq : semilinearAction 3 K A τ ^ 2 = 1 := by rw [← hAτ]; exact hsq0
        have hno := noA6_semilinear_three hO hK A hτ hsq
        rw [← hAτ] at hno
        exact fun D hD => (hno D hD).elim
    · refine SmallStmt.of_eq hA ?_
      intro D hD
      exact hgraph (f := 2) (by rw [hK]; norm_num) (by norm_num)
        (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) A (hA ▸ hσ) D hD
    · exact SmallStmt.of_eq hAτ fun D hD =>
        (graphField_three_false hO hK A hτ (hAτ ▸ hσ) hD).elim

theorem smallStmt_PSL_four (hgraph : PureGraphSmall) (hK : Nat.card K = 3)
    (σ : MulAut (ProjectiveSpecialLinearGroup (Fin 4) K)) (hσ : orderOf σ = 2) :
    SmallStmt .PSL 4 1 σ := by
  by_cases hin : σ ∈ (MulAut.conj : ProjectiveSpecialLinearGroup (Fin 4) K →*
      MulAut (ProjectiveSpecialLinearGroup (Fin 4) K)).range
  · obtain ⟨B, hB⟩ := exists_innerDiagonal_of_mem_range hin
    exact SmallStmt.of_eq hB (small_inner_four hK (hB ▸ hσ))
  · rcases normal_form_ge_three (by norm_num : 3 ≤ 4) σ with
      ⟨A, τ, hAτ⟩ | ⟨A, hA⟩ | ⟨A, τ, hτ, hAτ⟩
    · have hτ : τ = 1 := eq_one_of_card_three hK τ
      have h1 : σ = innerDiagonalAction 4 K A := by
        rw [hAτ, hτ, CatalogueBLinearSemilinear.semilinearAction_one_field]
      exact SmallStmt.of_eq h1 (small_inner_four hK (h1 ▸ hσ))
    · refine SmallStmt.of_eq hA ?_
      intro D hD
      exact hgraph (f := 1) (by rw [hK]; norm_num) (by norm_num)
        (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))) A (hA ▸ hσ) D hD
    · exact absurd (eq_one_of_card_three hK τ) hτ

end Assembly

end CFSG.ComponentClassification.CatFC.PSLSmall

namespace CFSG.ComponentClassification.CatFC

open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)

theorem oddA6Small_PSL_of_graph (hO : LieOrderFormulasInput) (hgraph : PSLSmall.PureGraphSmall) :
    OddA6Small .PSL := by
  apply oddA6Small_of_concrete
  intro S _ _ n p f hp hp2 hadm hm hp3 hshape
  subst hp3
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CatLeafProof.nonempty_mulEquiv_psl_of_lieModel hadm hm
  refine ⟨Matrix.ProjectiveSpecialLinearGroup (Fin n) K, inferInstance, inferInstance, e, ?_⟩
  intro σ D hσ hD
  rcases hshape with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | h | h | h | h | h | h
  · exact PSLSmall.smallStmt_PSL_two (by rw [hK]; norm_num) σ hσ D hD
  · exact PSLSmall.smallStmt_PSL_three hO hgraph (by rw [hK]; norm_num) σ hσ D hD
  · exact PSLSmall.smallStmt_PSL_four hgraph (by rw [hK]; norm_num) σ hσ D hD
  all_goals exact absurd h.1 (by decide)

end CFSG.ComponentClassification.CatFC
