module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphSpinFinalAgree
public import CFSG.RankThree.PartOne.AUTSL.Interface

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation
  slConjugation_matrix)
open CFSG.ComponentClassification.CatalogueBGraphForm (slGraphAut slGraphAut_matrix)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.Steinberg.TwistedE6 (sigma)
open CFSG.EvenSmallLie CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput)

section Beta

variable {K : Type} [Field K]

@[expose] def pairPerm4 : Equiv.Perm (Fin 4) :=
  ⟨![2, 3, 0, 1], ![2, 3, 0, 1], by decide, by decide⟩

@[expose] noncomputable def graphBeta4 : MulAut (SpecialLinearGroup (Fin 4) K) :=
  slConjugation 4 K (permGL pairPerm4) * slGraphAut 4 K

theorem graphBeta4_transvection {i j : Fin 4} (hij : i ≠ j) (c : K) :
    graphBeta4 (SpecialLinearGroup.transvection hij c) =
      SpecialLinearGroup.transvection (pairPerm4.symm.injective.ne hij.symm) (-c) := by
  rw [graphBeta4, MulAut.mul_apply, slGraphAut_transvection, slConjugation_permGL_transvection]

theorem coe_graphBeta4 (g : SpecialLinearGroup (Fin 4) K) :
    ((graphBeta4 g : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      ((permGL pairPerm4 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        ((g⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ *
          (((permGL pairPerm4)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
  rw [graphBeta4, MulAut.mul_apply, slConjugation_matrix, slGraphAut_matrix]

end Beta

section Commute

variable {K : Type} [Field K]

theorem mem_range_scalar_of_commute_gens {B : Matrix (Fin 4) (Fin 4) K}
    (h02 : Commute (single 0 2 1) B) (h20 : Commute (single 2 0 1) B)
    (h13 : Commute (single 1 3 1) B) (h31 : Commute (single 3 1 1) B)
    (h0132 : Commute (single 0 1 1 + single 3 2 1) B)
    (h1023 : Commute (single 1 0 1 + single 2 3 1) B) :
    B ∈ Set.range (Matrix.scalar (Fin 4)) := by
  have e : ∀ (i j k : Fin 4), (single i j 1 : Matrix (Fin 4) (Fin 4) K) * single j k 1 =
      single i k 1 := by
    intro i j k
    rw [single_mul_single_same, one_mul]
  have h00 : Commute (single (0 : Fin 4) 0 1 : Matrix (Fin 4) (Fin 4) K) B := by
    rw [← e 0 2 0]; exact h02.mul_left h20
  have h22 : Commute (single (2 : Fin 4) 2 1 : Matrix (Fin 4) (Fin 4) K) B := by
    rw [← e 2 0 2]; exact h20.mul_left h02
  have h11 : Commute (single (1 : Fin 4) 1 1 : Matrix (Fin 4) (Fin 4) K) B := by
    rw [← e 1 3 1]; exact h13.mul_left h31
  have h33 : Commute (single (3 : Fin 4) 3 1 : Matrix (Fin 4) (Fin 4) K) B := by
    rw [← e 3 1 3]; exact h31.mul_left h13
  have h01 : Commute ((single (0 : Fin 4) 1 1 : Matrix (Fin 4) (Fin 4) K)) B := by
    have : (single (0 : Fin 4) 0 1 : Matrix (Fin 4) (Fin 4) K) * (single 0 1 1 + single 3 2 1) =
        single 0 1 1 := by
      rw [mul_add, e, single_mul_single_of_ne _ _ _ _ (show (0 : Fin 4) ≠ 3 by decide), add_zero]
    rw [← this]
    exact h00.mul_left h0132
  have h32 : Commute ((single (3 : Fin 4) 2 1 : Matrix (Fin 4) (Fin 4) K)) B := by
    have : (single (3 : Fin 4) 3 1 : Matrix (Fin 4) (Fin 4) K) * (single 0 1 1 + single 3 2 1) =
        single 3 2 1 := by
      rw [mul_add, e, single_mul_single_of_ne _ _ _ _ (show (3 : Fin 4) ≠ 0 by decide), zero_add]
    rw [← this]
    exact h33.mul_left h0132
  have h10 : Commute ((single (1 : Fin 4) 0 1 : Matrix (Fin 4) (Fin 4) K)) B := by
    have : (single (1 : Fin 4) 1 1 : Matrix (Fin 4) (Fin 4) K) * (single 1 0 1 + single 2 3 1) =
        single 1 0 1 := by
      rw [mul_add, e, single_mul_single_of_ne _ _ _ _ (show (1 : Fin 4) ≠ 2 by decide), add_zero]
    rw [← this]
    exact h11.mul_left h1023
  have h23 : Commute ((single (2 : Fin 4) 3 1 : Matrix (Fin 4) (Fin 4) K)) B := by
    have : (single (2 : Fin 4) 2 1 : Matrix (Fin 4) (Fin 4) K) * (single 1 0 1 + single 2 3 1) =
        single 2 3 1 := by
      rw [mul_add, e, single_mul_single_of_ne _ _ _ _ (show (2 : Fin 4) ≠ 1 by decide), zero_add]
    rw [← this]
    exact h22.mul_left h1023
  have h03 : Commute (single (0 : Fin 4) 3 1 : Matrix (Fin 4) (Fin 4) K) B := by
    rw [← e 0 1 3]; exact h01.mul_left h13
  have h12 : Commute (single (1 : Fin 4) 2 1 : Matrix (Fin 4) (Fin 4) K) B := by
    rw [← e 1 0 2]; exact h10.mul_left h02
  have h21 : Commute (single (2 : Fin 4) 1 1 : Matrix (Fin 4) (Fin 4) K) B := by
    rw [← e 2 3 1]; exact h23.mul_left h31
  have h30 : Commute (single (3 : Fin 4) 0 1 : Matrix (Fin 4) (Fin 4) K) B := by
    rw [← e 3 2 0]; exact h32.mul_left h20
  refine mem_range_scalar_of_commute_single fun i j hij => ?_
  fin_cases i <;> fin_cases j
  all_goals first
    | exact absurd rfl hij
    | assumption

end Commute

section Rigid

variable {K : Type} [Field K]

theorem transvection_congr_of_eq {n : ℕ} {i j i' j' : Fin n} (hij : i ≠ j) (h' : i' ≠ j')
    (hi : i = i') (hj : j = j') {c c' : K} (hc : c = c') :
    SpecialLinearGroup.transvection hij c = SpecialLinearGroup.transvection h' c' := by
  subst hi hj hc
  rfl

theorem commute_of_conj_eq_conj {n : ℕ} {A P : GL (Fin n) K} {X : Matrix (Fin n) (Fin n) K}
    (h : (A : Matrix (Fin n) (Fin n) K) * X * ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (P : Matrix (Fin n) (Fin n) K) * X * ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    Commute X (((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * A) := by
  have hA : ∀ u : GL (Fin n) K, (u : Matrix (Fin n) (Fin n) K) *
      ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := fun u => by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hA' : ∀ u : GL (Fin n) K, ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (u : Matrix (Fin n) (Fin n) K) = 1 := fun u => by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  show X * (((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * A) =
    ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * A * X
  calc X * (((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * A) =
      ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((P : Matrix (Fin n) (Fin n) K) * X *
        ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * A := by
        simp only [← mul_assoc, hA', one_mul]
    _ = ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((A : Matrix (Fin n) (Fin n) K) * X *
        ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * A := by rw [h]
    _ = ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * A * X := by
        simp only [mul_assoc, hA', mul_one]

theorem conj_eq_conj_of_scalar {n : ℕ} {A P : GL (Fin n) K}
    (h : ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * A ∈ Set.range (Matrix.scalar (Fin n)))
    (X : Matrix (Fin n) (Fin n) K) :
    (A : Matrix (Fin n) (Fin n) K) * X * ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (P : Matrix (Fin n) (Fin n) K) * X * ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  obtain ⟨r, hr⟩ := h
  have hA : ∀ u : GL (Fin n) K, (u : Matrix (Fin n) (Fin n) K) *
      ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := fun u => by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hcomm : Commute (((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * A) X := by
    rw [← hr]
    exact Matrix.scalar_commute r (fun r' => Commute.all r r') X
  have hPA : (A : Matrix (Fin n) (Fin n) K) =
      (P : Matrix (Fin n) (Fin n) K) * (((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * A) := by
    rw [← mul_assoc, hA, one_mul]
  calc (A : Matrix (Fin n) (Fin n) K) * X * ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (P : Matrix (Fin n) (Fin n) K) * ((((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * A) *
        X) * ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        conv_lhs => rw [hPA]
        simp only [mul_assoc]
    _ = (P : Matrix (Fin n) (Fin n) K) * (X * (((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        A)) * ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [hcomm.eq]
    _ = _ := by simp only [mul_assoc, hA, mul_one]

end Rigid

section Main

variable {K : Type} [Field K] [CharP K 2]

theorem graphBeta4_transvection_eq {i j i' j' : Fin 4} (hij : i ≠ j) (h' : i' ≠ j')
    (hi : pairPerm4.symm j = i') (hj : pairPerm4.symm i = j') (c : K) :
    graphBeta4 (SpecialLinearGroup.transvection hij c) = SpecialLinearGroup.transvection h' c := by
  rw [graphBeta4_transvection]
  exact transvection_congr_of_eq _ _ hi hj (CharTwo.neg_eq c)

omit [CharP K 2] in
theorem transvection_commute_four {i j k l : Fin 4} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k)
    (hli : l ≠ i) (c d : K) :
    SpecialLinearGroup.transvection hij c * SpecialLinearGroup.transvection hkl d =
      SpecialLinearGroup.transvection hkl d * SpecialLinearGroup.transvection hij c := by
  apply Subtype.ext
  change (SpecialLinearGroup.transvection hij c : Matrix (Fin 4) (Fin 4) K) *
      (SpecialLinearGroup.transvection hkl d : Matrix (Fin 4) (Fin 4) K) =
    (SpecialLinearGroup.transvection hkl d : Matrix (Fin 4) (Fin 4) K) *
      (SpecialLinearGroup.transvection hij c : Matrix (Fin 4) (Fin 4) K)
  simp only [SpecialLinearGroup.transvection_coe, mul_add, add_mul,
    mul_one, one_mul, single_mul_single_of_ne _ _ _ _ hjk, single_mul_single_of_ne _ _ _ _ hli,
    add_zero]
  abel

theorem coe_transvection_inv_transpose {i j : Fin 4} (hij : i ≠ j) (c : K) :
    ((((SpecialLinearGroup.transvection hij c)⁻¹ : SpecialLinearGroup (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K))ᵀ = 1 + single j i c := by
  rw [SpecialLinearGroup.transvection_inv, SpecialLinearGroup.transvection_coe,
    transpose_add, transpose_one, transpose_single, CharTwo.neg_eq]

omit [CharP K 2] in
theorem map_one_add_single_one_four (ρ : K ≃+* K) (i j : Fin 4) :
    (1 + single i j (1 : K) : Matrix (Fin 4) (Fin 4) K).map ρ = 1 + single i j 1 := by
  ext a b
  simp only [map_apply, Matrix.add_apply, one_apply, single_apply]
  split_ifs <;> simp

omit [CharP K 2] in
theorem map_one_add_single_four (ρ : K ≃+* K) (i j : Fin 4) (c : K) :
    (1 + single i j c : Matrix (Fin 4) (Fin 4) K).map ρ = 1 + single i j (ρ c) := by
  ext a b
  simp only [map_apply, Matrix.add_apply, one_apply, single_apply]
  split_ifs <;> simp

omit [CharP K 2] in
theorem one_add_single_apply_of_ne {i j : Fin 4} (hij : i ≠ j) (c : K) :
    (1 + single i j c : Matrix (Fin 4) (Fin 4) K) i j = c := by
  rw [Matrix.add_apply, one_apply_ne hij, single_apply_same, zero_add]

omit [CharP K 2] in
theorem conj_left_cancel {n : ℕ} {P : GL (Fin n) K} {X X' : Matrix (Fin n) (Fin n) K}
    (h : (P : Matrix (Fin n) (Fin n) K) * X * ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (P : Matrix (Fin n) (Fin n) K) * X' * ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    X = X' := by
  have hA : (P : Matrix (Fin n) (Fin n) K) *
      ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hA' : ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (P : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc X = (((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * P) * X *
        (((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * P) := by rw [hA', one_mul, mul_one]
    _ = ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((P : Matrix (Fin n) (Fin n) K) * X *
        ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * P := by simp only [mul_assoc]
    _ = ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((P : Matrix (Fin n) (Fin n) K) * X' *
        ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * P := by rw [h]
    _ = (((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * P) * X' *
        (((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * P) := by simp only [mul_assoc]
    _ = X' := by rw [hA', one_mul, mul_one]

theorem eq_one_or_eq_graphBeta4 [Finite K] (θ : MulAut (SpecialLinearGroup (Fin 4) K))
    (hfix : ∀ g, graphBeta4 g = g → θ g = g) : θ = 1 ∨ θ = graphBeta4 := by
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  have h20 : (2 : Fin 4) ≠ 0 := by decide
  have h13 : (1 : Fin 4) ≠ 3 := by decide
  have h31 : (3 : Fin 4) ≠ 1 := by decide
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h32 : (3 : Fin 4) ≠ 2 := by decide
  have h10 : (1 : Fin 4) ≠ 0 := by decide
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  have f02 : ∀ c : K, graphBeta4 (SpecialLinearGroup.transvection h02 c) =
      SpecialLinearGroup.transvection h02 c := fun c =>
    graphBeta4_transvection_eq h02 h02 (by decide) (by decide) c
  have f20 : graphBeta4 (SpecialLinearGroup.transvection h20 (1 : K)) =
      SpecialLinearGroup.transvection h20 1 :=
    graphBeta4_transvection_eq h20 h20 (by decide) (by decide) 1
  have f13 : graphBeta4 (SpecialLinearGroup.transvection h13 (1 : K)) =
      SpecialLinearGroup.transvection h13 1 :=
    graphBeta4_transvection_eq h13 h13 (by decide) (by decide) 1
  have f31 : graphBeta4 (SpecialLinearGroup.transvection h31 (1 : K)) =
      SpecialLinearGroup.transvection h31 1 :=
    graphBeta4_transvection_eq h31 h31 (by decide) (by decide) 1
  have f0132 : graphBeta4 (SpecialLinearGroup.transvection h01 (1 : K) *
      SpecialLinearGroup.transvection h32 1) =
        SpecialLinearGroup.transvection h01 1 * SpecialLinearGroup.transvection h32 1 := by
    rw [map_mul, graphBeta4_transvection_eq h01 h32 (by decide) (by decide),
      graphBeta4_transvection_eq h32 h01 (by decide) (by decide)]
    exact (transvection_commute_four h01 h32 (by decide) (by decide) 1 1).symm
  have f1023 : graphBeta4 (SpecialLinearGroup.transvection h10 (1 : K) *
      SpecialLinearGroup.transvection h23 1) =
        SpecialLinearGroup.transvection h10 1 * SpecialLinearGroup.transvection h23 1 := by
    rw [map_mul, graphBeta4_transvection_eq h10 h23 (by decide) (by decide),
      graphBeta4_transvection_eq h23 h10 (by decide) (by decide)]
    exact (transvection_commute_four h10 h23 (by decide) (by decide) 1 1).symm
  have mT : ∀ {i j : Fin 4} (h : i ≠ j) (c : K),
      ((SpecialLinearGroup.transvection h c : SpecialLinearGroup (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) = 1 + single i j c := fun h c =>
    SpecialLinearGroup.transvection_coe h c
  have mP : ∀ {i j k l : Fin 4} (h : i ≠ j) (h' : k ≠ l), j ≠ k →
      ((SpecialLinearGroup.transvection h (1 : K) * SpecialLinearGroup.transvection h' 1 :
        SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        1 + (single i j 1 + single k l 1) := by
    intro i j k l h h' hjk
    change ((SpecialLinearGroup.transvection h (1 : K) : SpecialLinearGroup (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) * (SpecialLinearGroup.transvection h' 1 :
          SpecialLinearGroup (Fin 4) K) = _
    rw [mT, mT, mul_add, add_mul, add_mul, one_mul, mul_one, one_mul,
      single_mul_single_of_ne _ _ _ _ hjk, add_zero]
    abel
  have mPinv : ∀ {i j k l : Fin 4} (h : i ≠ j) (h' : k ≠ l), l ≠ i →
      (((SpecialLinearGroup.transvection h (1 : K) * SpecialLinearGroup.transvection h' 1)⁻¹ :
        SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ =
        1 + (single j i 1 + single l k 1) := by
    intro i j k l h h' hli
    rw [_root_.mul_inv_rev]
    change ((((SpecialLinearGroup.transvection h' (1 : K))⁻¹ : SpecialLinearGroup (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) * (((SpecialLinearGroup.transvection h 1)⁻¹ :
          SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))ᵀ = _
    rw [transpose_mul, coe_transvection_inv_transpose, coe_transvection_inv_transpose, mul_add,
      add_mul, add_mul, one_mul, mul_one, one_mul, single_mul_single_of_ne _ _ _ _ hli.symm,
      add_zero]
    abel
  have hρ1 : ∀ (ρ : K ≃+* K) (i j k l : Fin 4),
      (1 + (single i j (1 : K) + single k l 1) : Matrix (Fin 4) (Fin 4) K).map ρ =
        1 + (single i j 1 + single k l 1) := by
    intro ρ i j k l
    ext a b
    simp only [map_apply, Matrix.add_apply, one_apply, single_apply]
    split_ifs <;> simp
  have sub1 : ∀ {N B : Matrix (Fin 4) (Fin 4) K}, Commute (1 + N) B → Commute N B := by
    intro N B h
    simpa using h.sub_left (Commute.one_left B)
  obtain ⟨A, ρ, hθ | hθ⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_matrix_form_of_mulAut_sl (by norm_num) θ
  ·
    have hc : ∀ g : SpecialLinearGroup (Fin 4) K, graphBeta4 g = g →
        (g : Matrix (Fin 4) (Fin 4) K).map ρ = g →
        Commute (g : Matrix (Fin 4) (Fin 4) K) ((((1 : GL (Fin 4) K))⁻¹ : GL (Fin 4) K) *
          A : Matrix (Fin 4) (Fin 4) K) := by
      intro g hg hm
      apply commute_of_conj_eq_conj
      have h1 := hθ g
      rw [hfix g hg, hm] at h1
      rw [inv_one, Units.val_one, one_mul, mul_one]
      exact h1.symm
    set B : Matrix (Fin 4) (Fin 4) K := (((1 : GL (Fin 4) K))⁻¹ : GL (Fin 4) K) * A with hB
    have c02 : Commute (single 0 2 (1 : K)) B := sub1 (by
      rw [← mT h02]
      exact hc _ (f02 1) (by rw [mT]; exact map_one_add_single_one_four ρ _ _))
    have c20 : Commute (single 2 0 (1 : K)) B := sub1 (by
      rw [← mT h20]
      exact hc _ f20 (by rw [mT]; exact map_one_add_single_one_four ρ _ _))
    have c13 : Commute (single 1 3 (1 : K)) B := sub1 (by
      rw [← mT h13]
      exact hc _ f13 (by rw [mT]; exact map_one_add_single_one_four ρ _ _))
    have c31 : Commute (single 3 1 (1 : K)) B := sub1 (by
      rw [← mT h31]
      exact hc _ f31 (by rw [mT]; exact map_one_add_single_one_four ρ _ _))
    have c0132 : Commute (single 0 1 (1 : K) + single 3 2 1) B := sub1 (by
      rw [← mP h01 h32 (by decide)]
      exact hc _ f0132 (by rw [mP h01 h32 (by decide)]; exact hρ1 ρ _ _ _ _))
    have c1023 : Commute (single 1 0 (1 : K) + single 2 3 1) B := sub1 (by
      rw [← mP h10 h23 (by decide)]
      exact hc _ f1023 (by rw [mP h10 h23 (by decide)]; exact hρ1 ρ _ _ _ _))
    have hX := conj_eq_conj_of_scalar (A := A) (P := 1)
      (mem_range_scalar_of_commute_gens c02 c20 c13 c31 c0132 c1023)
    have hρid : ∀ c : K, ρ c = c := by
      intro c
      have h1 := hθ (SpecialLinearGroup.transvection h02 c)
      rw [hfix _ (f02 c), hX, inv_one, Units.val_one, one_mul, mul_one, mT,
        map_one_add_single_four] at h1
      have h2 := congrFun (congrFun h1 0) 2
      rwa [one_add_single_apply_of_ne h02, one_add_single_apply_of_ne h02, eq_comm] at h2
    refine .inl (MulEquiv.ext fun g => Subtype.ext ?_)
    rw [hθ g, hX, inv_one, Units.val_one, one_mul, mul_one]
    ext a b
    simp [hρid]
  ·
    have hc : ∀ g : SpecialLinearGroup (Fin 4) K, graphBeta4 g = g →
        (((g⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ).map ρ =
          ((g⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ →
        Commute (((g⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ)
          ((((permGL pairPerm4 : GL (Fin 4) K))⁻¹ : GL (Fin 4) K) * A :
            Matrix (Fin 4) (Fin 4) K) := by
      intro g hg hm
      apply commute_of_conj_eq_conj
      have h1 := hθ g
      rw [hfix g hg, hm] at h1
      have h2 := coe_graphBeta4 g
      rw [hg] at h2
      rw [← h1, ← h2]
    set B : Matrix (Fin 4) (Fin 4) K :=
      (((permGL pairPerm4 : GL (Fin 4) K))⁻¹ : GL (Fin 4) K) * A with hB
    have c20 : Commute (single 2 0 (1 : K)) B := sub1 (by
      rw [← coe_transvection_inv_transpose h02]
      exact hc _ (f02 1) (by
        rw [coe_transvection_inv_transpose]
        exact map_one_add_single_one_four ρ _ _))
    have c02 : Commute (single 0 2 (1 : K)) B := sub1 (by
      rw [← coe_transvection_inv_transpose h20]
      exact hc _ f20 (by
        rw [coe_transvection_inv_transpose]
        exact map_one_add_single_one_four ρ _ _))
    have c31 : Commute (single 3 1 (1 : K)) B := sub1 (by
      rw [← coe_transvection_inv_transpose h13]
      exact hc _ f13 (by
        rw [coe_transvection_inv_transpose]
        exact map_one_add_single_one_four ρ _ _))
    have c13 : Commute (single 1 3 (1 : K)) B := sub1 (by
      rw [← coe_transvection_inv_transpose h31]
      exact hc _ f31 (by
        rw [coe_transvection_inv_transpose]
        exact map_one_add_single_one_four ρ _ _))
    have c1023 : Commute (single 1 0 (1 : K) + single 2 3 1) B := sub1 (by
      rw [← mPinv h01 h32 (by decide)]
      exact hc _ f0132 (by rw [mPinv h01 h32 (by decide)]; exact hρ1 ρ _ _ _ _))
    have c0132 : Commute (single 0 1 (1 : K) + single 3 2 1) B := sub1 (by
      rw [← mPinv h10 h23 (by decide)]
      exact hc _ f1023 (by rw [mPinv h10 h23 (by decide)]; exact hρ1 ρ _ _ _ _))
    have hX := conj_eq_conj_of_scalar (A := A) (P := permGL pairPerm4)
      (mem_range_scalar_of_commute_gens c02 c20 c13 c31 c0132 c1023)
    have hρid : ∀ c : K, ρ c = c := by
      intro c
      have h1 := hθ (SpecialLinearGroup.transvection h02 c)
      rw [hfix _ (f02 c), hX] at h1
      have h2 := coe_graphBeta4 (SpecialLinearGroup.transvection h02 c)
      rw [f02 c] at h2
      have h3 := conj_left_cancel (h2.symm.trans h1)
      rw [coe_transvection_inv_transpose, map_one_add_single_four] at h3
      have h4 := congrFun (congrFun h3 2) 0
      rwa [one_add_single_apply_of_ne h20, one_add_single_apply_of_ne h20, eq_comm] at h4
    refine .inr (MulEquiv.ext fun g => Subtype.ext ?_)
    rw [hθ g, hX, coe_graphBeta4]
    congr 2
    ext a b
    simp [hρid]

end Main

section Transport

variable {K : Type} [Field K]

@[expose] def blockFourEquiv : Fin 4 ≃ {x : Fin 6 // x ∈ lin6BlockA} where
  toFun k := ⟨![1, 2, 4, 5] k, by fin_cases k <;> decide⟩
  invFun x := if x.1 = 1 then 0 else if x.1 = 2 then 1 else if x.1 = 4 then 2 else 3
  left_inv k := by fin_cases k <;> rfl
  right_inv x := by
    obtain ⟨x, hx⟩ := x
    simp only [lin6BlockA, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> rfl

@[expose] noncomputable def blockFourHom :
    SpecialLinearGroup (Fin 4) K →* SpecialLinearGroup (Fin 6) K :=
  (CFSG.SeitzReduction.LinearPilot.blockEmbed lin6BlockA).comp
    (CFSG.SeitzReduction.LinearPilot.reindexSpecialLinear blockFourEquiv).toMonoidHom

theorem blockFourHom_injective : Function.Injective (blockFourHom (K := K)) :=
  (CFSG.SeitzReduction.LinearPilot.blockEmbed_injective _).comp
    (CFSG.SeitzReduction.LinearPilot.reindexSpecialLinear blockFourEquiv).injective

theorem range_blockFourHom :
    (blockFourHom (K := K)).range =
      CFSG.SeitzReduction.LinearPilot.blockSpecialLinear lin6BlockA := by
  rw [blockFourHom, MonoidHom.range_comp, MonoidHom.range_eq_top.2
    (CFSG.SeitzReduction.LinearPilot.reindexSpecialLinear blockFourEquiv).surjective,
    ← MonoidHom.range_eq_map, CFSG.SeitzReduction.LinearPilot.range_blockEmbed]

theorem blockFourHom_transvection {a b : Fin 4} (hab : a ≠ b) (c : K) :
    blockFourHom (SpecialLinearGroup.transvection hab c) =
      SpecialLinearGroup.transvection
        (fun h => blockFourEquiv.injective.ne hab (Subtype.ext h) :
          (blockFourEquiv a : Fin 6) ≠ blockFourEquiv b) c := by
  have h1 : CFSG.SeitzReduction.LinearPilot.reindexSpecialLinear blockFourEquiv
      (SpecialLinearGroup.transvection hab c) =
        SpecialLinearGroup.transvection (blockFourEquiv.injective.ne hab) c := by
    apply Subtype.ext
    change Matrix.reindex blockFourEquiv blockFourEquiv (1 + Matrix.single a b c) =
      1 + Matrix.single (blockFourEquiv a) (blockFourEquiv b) c
    rw [Matrix.reindex_apply, show (1 + Matrix.single a b c).submatrix blockFourEquiv.symm
        blockFourEquiv.symm = (1 : Matrix (Fin 4) (Fin 4) K).submatrix blockFourEquiv.symm
          blockFourEquiv.symm + (Matrix.single a b c).submatrix blockFourEquiv.symm
            blockFourEquiv.symm from rfl,
      Matrix.submatrix_one_equiv, Matrix.submatrix_single_equiv, Equiv.symm_symm]
  rw [blockFourHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1,
    CFSG.SeitzReduction.LinearPilot.blockEmbed_transvection]

theorem graphBeta6_blockFourHom (g : SpecialLinearGroup (Fin 4) K) :
    (slConjugation 6 K (graphGram6 K) * slGraphAut 6 K) (blockFourHom g) =
      blockFourHom (graphBeta4 g) := by
  have h : ((slConjugation 6 K (graphGram6 K) * slGraphAut 6 K).toMonoidHom.comp blockFourHom) =
      blockFourHom.comp (graphBeta4 (K := K)).toMonoidHom := by
    refine MonoidHom.eq_of_eqOn_dense
      (Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field) ?_
    rintro _ ⟨⟨a, b, hab, c⟩, rfl⟩
    simp only [Matrix.TransvectionStruct.toSpecialLinearGroup_mk, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom]
    rw [blockFourHom_transvection, graphBeta6_transvection, graphBeta4_transvection,
      blockFourHom_transvection]
    have key : ∀ x : Fin 4, graphPairPerm.symm (blockFourEquiv x : Fin 6) =
        (blockFourEquiv (pairPerm4.symm x) : Fin 6) := by decide
    exact transvection_congr_of_eq _ _ (key b) (key a) rfl
  exact DFunLike.congr_fun h g

end Transport

section Rigidity

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem range_graphParamHom_comp_blockFourHom :
    ((graphParamHom K (RingEquiv.refl K)).comp blockFourHom).range = e6ScLevi K e6A3Nodes := by
  rw [MonoidHom.range_comp, range_blockFourHom, e6ScLevi_A3_eq_map_blockSpecialLinear]

variable (K) in
@[expose] noncomputable def blockFourEquivA3 :
    SpecialLinearGroup (Fin 4) K ≃* e6ScLevi K e6A3Nodes :=
  (MonoidHom.ofInjective (f := (graphParamHom K (RingEquiv.refl K)).comp blockFourHom)
    ((graphParamHom_injective (RingEquiv.refl K)).comp blockFourHom_injective)).trans
    (MulEquiv.subgroupCongr range_graphParamHom_comp_blockFourHom)

theorem coe_blockFourEquivA3 (g : SpecialLinearGroup (Fin 4) K) :
    ((blockFourEquivA3 K g : e6ScLevi K e6A3Nodes) : e6Data_valid.minGroup K) =
      graphParamHom K (RingEquiv.refl K) (blockFourHom g) :=
  rfl

theorem sigma_blockFourEquivA3 (g : SpecialLinearGroup (Fin 4) K) :
    sigma K (RingHom.id K) (blockFourEquivA3 K g : e6Data_valid.minGroup K) =
      blockFourEquivA3 K (graphBeta4 g) := by
  rw [coe_blockFourEquivA3, coe_blockFourEquivA3, sigma_graphParamHom, graphBeta6_blockFourHom]

end Rigidity

section Holds

theorem e6RowA3RigidityInput_holds : E6RowA3RigidityInput := by
  intro K _ _ _ _ θ hfix _
  set Ψ := blockFourEquivA3 K with hΨ
  set θ4 : MulAut (SpecialLinearGroup (Fin 4) K) := (Ψ.trans θ).trans Ψ.symm with hθ4def
  have hθ4 : ∀ g, graphBeta4 g = g → θ4 g = g := by
    intro g hg
    have hs : sigma K (RingHom.id K) ((Ψ g : e6ScLevi K e6A3Nodes) :
        e6Data_valid.minGroup K) = Ψ g := by
      rw [hΨ, sigma_blockFourEquivA3, hg]
    rw [hθ4def, MulEquiv.trans_apply, MulEquiv.trans_apply, hfix (Ψ g) hs,
      MulEquiv.symm_apply_apply]
  rcases eq_one_or_eq_graphBeta4 θ4 hθ4 with h | h
  · refine .inl fun x => ?_
    obtain ⟨g, rfl⟩ := Ψ.surjective x
    have h1 := DFunLike.congr_fun h g
    rw [hθ4def, MulEquiv.trans_apply, MulEquiv.trans_apply, MulAut.one_apply,
      MulEquiv.symm_apply_eq] at h1
    exact h1
  · refine .inr fun x y hxy => ?_
    obtain ⟨g, rfl⟩ := Ψ.surjective x
    have h1 := DFunLike.congr_fun h g
    rw [hθ4def, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_eq] at h1
    rw [h1]
    apply Subtype.ext
    rw [hxy, hΨ, sigma_blockFourEquivA3]

end Holds

section Corollaries

theorem e6GraphRowSpinNormInput_of_sp4Model (hM : E6RowSp4ModelInput) :
    E6GraphRowSpinNormInput :=
  e6GraphRowSpinNormInput_of_models hM e6RowA3RigidityInput_holds

end Corollaries

end CFSG.SeitzReduction.F4Pilot
