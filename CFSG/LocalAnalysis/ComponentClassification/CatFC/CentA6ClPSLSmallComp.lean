module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddPSL
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClExcCommon

public noncomputable section

namespace CFSG.ComponentClassification.CatFC.PSLSmall

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Matrix
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)
open CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatalogueBHigherLinearField (fixedField pslFieldAut)

theorem false_of_card_lie_model (hO : LieOrderFormulasInput) {Y : Type} [Group Y]
    (hY : Nat.card Y = 360) {τ : StatedLieTag} {n p f : ℕ}
    (hadm : StatedLieAdmissible τ n p f) (hp2 : p ≠ 2) (hm : Blueprint.LieModel Y τ n p f)
    (hne : ¬ (τ = .PSL ∧ n = 2)) : False :=
  hne (lieModel_dvd_360 hO hadm hp2 hm (by rw [hY]))

theorem field_three_false (hO : LieOrderFormulasInput) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 9) {τ : K ≃+* K} (hτ2 : τ ^ 2 = 1) (hτ : τ ≠ 1)
    {D : Subgroup ↥(fixedSubgroup (pslFieldAut (Fin 3) K τ))}
    (h : A6Hyp (pslFieldAut (Fin 3) K τ) D) : False := by
  obtain ⟨hcard, -, -, hiso⟩ :=
    CatalogueBHigherLinearField.linear_field_involution_fixed_p_components 3 (by norm_num) K τ
      hτ2 hτ
  have hq0 : Nat.card (fixedField K τ) = 3 := by
    have h2 : Nat.card (fixedField K τ) ^ 2 = 3 ^ 2 := by
      rw [← hcard, hK]
      norm_num
    exact Nat.pow_left_injective two_ne_zero h2
  have hex : ¬ (3 = 2 ∧ (Nat.card (fixedField K τ) = 2 ∨ Nat.card (fixedField K τ) = 3)) := by
    omega
  have hD2 : IsPComponent 2 D := isPComponent_two_of_isComponent h.component.1
  let D' : Subgroup ↥(CatalogueBHigherLinearField.fixedPSL 3 K τ) := D
  have hD' : Nat.card ↥D' = 360 := h.card_D
  obtain ⟨E⟩ := hiso hex 2 Nat.prime_two D' hD2
  have hadm : StatedLieAdmissible .PSL 3 3 1 :=
    ⟨Nat.prime_three, le_rfl, by norm_num, by decide, by decide⟩
  have hstated : StatedClassicalModel (ProjectiveSpecialLinearGroup (Fin 3) (fixedField K τ))
      .PSL 3 3 1 :=
    ⟨hadm, fixedField K τ, inferInstance, inferInstance, by rw [hq0]; norm_num,
      ⟨projectiveSpecialLinearGroupEquivStatedProj 3 _⟩⟩
  have hY : Nat.card (ProjectiveSpecialLinearGroup (Fin 3) (fixedField K τ)) = 360 := by
    rw [← Nat.card_congr E.toEquiv]
    exact hD'
  exact false_of_card_lie_model hO hY hadm (by norm_num) (Or.inl ⟨by decide, hstated⟩) (by simp)

theorem graphField_three_false (hO : LieOrderFormulasInput) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 9) (A : GL (Fin 3) K) {τ : K ≃+* K} (hτ : τ ≠ 1)
    (hord : orderOf (CatalogueBGraphField.graphFieldAction 3 K A τ) = 2)
    {D : Subgroup ↥(fixedSubgroup (CatalogueBGraphField.graphFieldAction 3 K A τ))}
    (h : A6Hyp (CatalogueBGraphField.graphFieldAction 3 K A τ) D) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsq : CatalogueBGraphField.graphFieldAction 3 K A τ ^ 2 = 1 := by
    rw [← hord]; exact pow_orderOf_eq_one _
  have hne1 : CatalogueBGraphField.graphFieldAction 3 K A τ ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hord
    exact absurd hord (by decide)
  obtain ⟨-, hhalf, hunitary, -, -, -, hcomp⟩ :=
    CatalogueBGraphField.odd_linear_graph_field_involution_fixed_p_components_native 3 K 3 2
      (by decide) (by norm_num) (by rw [hK]; norm_num) (by norm_num) A τ hτ hne1 hsq
  have hD2 : IsPComponent 2 D := isPComponent_two_of_isComponent h.component.1
  let D' : Subgroup ↥(CatalogueBGraphField.twistedFixedPSL 3 K A τ) := D
  have hD' : Nat.card ↥D' = 360 := h.card_D
  obtain ⟨-, ⟨E⟩⟩ := hcomp 2 Nat.prime_two D' hD2
  obtain ⟨eQ⟩ := nonempty_projectiveSpecialUnitary_equiv_statedProj (n := 3) (K := K) (p := 3)
    (e := 1) (by simpa using hunitary)
  have hadm : StatedLieAdmissible .PSU 3 3 1 :=
    ⟨Nat.prime_three, le_rfl, by norm_num, by decide⟩
  have hstated : StatedClassicalModel (StatedProj (StatedSU 3 (3 ^ 1) K)) .PSU 3 3 1 :=
    ⟨hadm, K, inferInstance, inferInstance, by simpa using hunitary, ⟨MulEquiv.refl _⟩⟩
  have hY : Nat.card (StatedProj (StatedSU 3 (3 ^ 1) K)) = 360 := by
    rw [← Nat.card_congr eQ.toEquiv, ← Nat.card_congr E.toEquiv]
    exact hD'
  exact false_of_card_lie_model hO hY hadm (by norm_num) (Or.inl ⟨by decide, hstated⟩) (by simp)

end CFSG.ComponentClassification.CatFC.PSLSmall
