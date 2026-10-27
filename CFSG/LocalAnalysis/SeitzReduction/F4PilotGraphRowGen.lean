module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphParamSLGraph
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphTorusEmbed

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open CFSG.ComponentClassification.CatalogueBGraphForm (slGraphAut)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Transvection

variable {n : ℕ} {F : Type} [Field F]

theorem slTransvection_commutator_formula {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (a b : F) :
    SpecialLinearGroup.transvection hij a * SpecialLinearGroup.transvection hjk b *
        (SpecialLinearGroup.transvection hij a)⁻¹ * (SpecialLinearGroup.transvection hjk b)⁻¹ =
      SpecialLinearGroup.transvection hik (a * b) := by
  rw [SpecialLinearGroup.transvection_inv, SpecialLinearGroup.transvection_inv]
  refine Subtype.ext ?_
  have hji : j ≠ i := hij.symm
  have hkj : k ≠ j := hjk.symm
  have hki : k ≠ i := hik.symm
  simp [SpecialLinearGroup.transvection_coe, mul_add, add_mul, single_mul_single_of_ne, hji, hkj,
    hki]
  rw [← Matrix.single_neg, ← Matrix.single_neg, ← Matrix.single_neg]
  abel

theorem slTransvection_commute {i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k)
    (hli : l ≠ i) (a b : F) :
    SpecialLinearGroup.transvection hij a * SpecialLinearGroup.transvection hkl b =
      SpecialLinearGroup.transvection hkl b * SpecialLinearGroup.transvection hij a := by
  refine Subtype.ext ?_
  simp [SpecialLinearGroup.transvection_coe, mul_add, add_mul, single_mul_single_of_ne, hjk, hli]
  abel

end Transvection

section Block

variable {F : Type} [Field F]

@[expose] def sl6BlockAIdx : Finset (Fin 6) := {1, 2, 4, 5}

@[expose] def sl6BlockA (F : Type) [Field F] : Subgroup (SpecialLinearGroup (Fin 6) F) :=
  closure {g | ∃ (i j : Fin 6) (hij : i ≠ j) (c : F), i ∈ sl6BlockAIdx ∧ j ∈ sl6BlockAIdx ∧
    g = SpecialLinearGroup.transvection hij c}

theorem transvection_mem_sl6BlockA {i j : Fin 6} (hij : i ≠ j) (hi : i ∈ sl6BlockAIdx)
    (hj : j ∈ sl6BlockAIdx) (c : F) : SpecialLinearGroup.transvection hij c ∈ sl6BlockA F :=
  subset_closure ⟨i, j, hij, c, hi, hj, rfl⟩

theorem exists_third_sl6BlockAIdx : ∀ i j : Fin 6, i ∈ sl6BlockAIdx → j ∈ sl6BlockAIdx →
    ∃ k : Fin 6, k ∈ sl6BlockAIdx ∧ i ≠ k ∧ k ≠ j := by
  decide

theorem commutator_sl6BlockA : ⁅sl6BlockA F, sl6BlockA F⁆ = sl6BlockA F := by
  refine le_antisymm (commutator_le_self _) ((closure_le _).2 ?_)
  rintro _ ⟨i, j, hij, c, hi, hj, rfl⟩
  obtain ⟨k, hk, hik, hkj⟩ := exists_third_sl6BlockAIdx i j hi hj
  have h := slTransvection_commutator_formula hik hkj hij c (1 : F)
  rw [mul_one] at h
  rw [← h]
  exact commutator_mem_commutator (transvection_mem_sl6BlockA hik hi hk c)
    (transvection_mem_sl6BlockA hkj hk hj 1)

theorem lin6Torus_sp6ParamA_apply (a : Fˣ) {i : Fin 6} (hi : i ∈ sl6BlockAIdx) :
    ((lin6Torus F (sp6ParamA F a) : SpecialLinearGroup (Fin 6) F) :
      Matrix (Fin 6) (Fin 6) F) i i = 1 := by
  rw [lin6Torus, coe_diagTorusSL]
  simp only [sl6BlockAIdx, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl <;>
    simp [Matrix.diagonal_apply_eq, sp6ParamA, lin6Weights]

theorem transvection_mul_diagonal_comm {n : ℕ} {i j : Fin n} (hij : i ≠ j) (c : F)
    {d : Fin n → F} (hd : d i = d j) :
    ((SpecialLinearGroup.transvection hij c : SpecialLinearGroup (Fin n) F) :
        Matrix (Fin n) (Fin n) F) * Matrix.diagonal d =
      Matrix.diagonal d *
        (SpecialLinearGroup.transvection hij c : SpecialLinearGroup (Fin n) F) := by
  rw [SpecialLinearGroup.transvection_coe, add_mul, mul_add, one_mul, mul_one]
  congr 1
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    rw [hd, mul_comm]
  · rw [zero_mul, mul_zero]

theorem sl6BlockA_le_centralizer :
    sl6BlockA F ≤ centralizer
      (((sp6TorusA (⊤ : Subgroup Fˣ)).map (sp6ToSL6 (F := F))) :
        Set (SpecialLinearGroup (Fin 6) F)) := by
  refine (closure_le _).2 ?_
  rintro _ ⟨i, j, hij, c, hi, hj, rfl⟩
  rw [SetLike.mem_coe, mem_centralizer_iff]
  rintro _ ⟨_, ⟨a, -, rfl⟩, rfl⟩
  refine Subtype.ext ?_
  change ((sp6ToSL6 (sp6Diag F (sp6ParamA F a)) : SpecialLinearGroup (Fin 6) F) :
      Matrix (Fin 6) (Fin 6) F) *
        (SpecialLinearGroup.transvection hij c : Matrix.SpecialLinearGroup (Fin 6) F) =
    (SpecialLinearGroup.transvection hij c : SpecialLinearGroup (Fin 6) F) *
      (sp6ToSL6 (sp6Diag F (sp6ParamA F a)) : SpecialLinearGroup (Fin 6) F)
  rw [sp6ToSL6_sp6Diag, lin6Torus, coe_diagTorusSL]
  refine (transvection_mul_diagonal_comm hij c ?_).symm
  have h1 := lin6Torus_sp6ParamA_apply a hi
  have h2 := lin6Torus_sp6ParamA_apply a hj
  rw [lin6Torus, coe_diagTorusSL, Matrix.diagonal_apply_eq] at h1 h2
  rw [h1, h2]

end Block

section Generation

variable {F : Type} [Field F]

theorem slTransvection_eq_of_eq {n : ℕ} {i j i' j' : Fin n} (hij : i ≠ j) (hij' : i' ≠ j')
    (hi : i = i') (hj : j = j') {c c' : F} (hc : c = c') :
    SpecialLinearGroup.transvection hij c = SpecialLinearGroup.transvection hij' c' := by
  subst hi hj hc
  rfl

@[expose] def SL6TrIn (H : Subgroup (SpecialLinearGroup (Fin 6) F)) (i j : Fin 6) : Prop :=
  ∀ (h : i ≠ j) (c : F), SpecialLinearGroup.transvection h c ∈ H

theorem SL6TrIn.trans {H : Subgroup (SpecialLinearGroup (Fin 6) F)} {i j k : Fin 6}
    (h₁ : SL6TrIn H i j) (h₂ : SL6TrIn H j k) (hij : i ≠ j) (hjk : j ≠ k) : SL6TrIn H i k := by
  intro hik c
  have h := slTransvection_commutator_formula hij hjk hik c (1 : F)
  rw [mul_one] at h
  rw [← h]
  exact mul_mem (mul_mem (mul_mem (h₁ hij c) (h₂ hjk 1)) (inv_mem (h₁ hij c)))
    (inv_mem (h₂ hjk 1))

theorem graphPairPerm_symm_apply : ∀ i : Fin 6, graphPairPerm.symm i = graphPairPerm i := by
  decide

theorem graphPairPerm_graphPairPerm : ∀ i : Fin 6, graphPairPerm (graphPairPerm i) = i := by
  decide

theorem graphBeta6_transvection_pair [CharP F 2] {i j : Fin 6} (hij : i ≠ j)
    (hj : graphPairPerm i = j) (c : F) :
    (slConjugation 6 F (graphGram6 F) * slGraphAut 6 F)
        (SpecialLinearGroup.transvection hij c) = SpecialLinearGroup.transvection hij c := by
  rw [graphBeta6_transvection]
  refine slTransvection_eq_of_eq _ _ ?_ ?_ (CharTwo.neg_eq c)
  · rw [graphPairPerm_symm_apply, ← hj, graphPairPerm_graphPairPerm]
  · rw [graphPairPerm_symm_apply, ← hj]

variable [CharP F 2]

theorem transvection_mem_range_sp6ToSL6 {i j : Fin 6} (hij : i ≠ j) (hj : graphPairPerm i = j)
    (c : F) : SpecialLinearGroup.transvection hij c ∈ (sp6ToSL6 (F := F)).range := by
  rw [← fixedSubgroup_graphGram6]
  exact graphBeta6_transvection_pair hij hj c

theorem transvection_mul_mem_range_sp6ToSL6 {i j i' j' : Fin 6} (hij : i ≠ j) (hij' : i' ≠ j')
    (hi' : graphPairPerm j = i') (hj' : graphPairPerm i = j') (hji' : j ≠ i') (hj'i : j' ≠ i)
    (c : F) :
    SpecialLinearGroup.transvection hij c * SpecialLinearGroup.transvection hij' c ∈
      (sp6ToSL6 (F := F)).range := by
  rw [← fixedSubgroup_graphGram6]
  change (slConjugation 6 F (graphGram6 F) * slGraphAut 6 F)
      (SpecialLinearGroup.transvection hij c * SpecialLinearGroup.transvection hij' c) =
    SpecialLinearGroup.transvection hij c * SpecialLinearGroup.transvection hij' c
  rw [map_mul, graphBeta6_transvection, graphBeta6_transvection,
    slTransvection_commute hij hij' hji' hj'i]
  congr 1
  · refine slTransvection_eq_of_eq _ _ ?_ ?_ (CharTwo.neg_eq c)
    · rw [graphPairPerm_symm_apply]
      exact hi'
    · rw [graphPairPerm_symm_apply]
      exact hj'
  · refine slTransvection_eq_of_eq _ _ ?_ ?_ (CharTwo.neg_eq c)
    · rw [graphPairPerm_symm_apply, ← hj', graphPairPerm_graphPairPerm]
    · rw [graphPairPerm_symm_apply, ← hi', graphPairPerm_graphPairPerm]

theorem range_sp6ToSL6_sup_sl6BlockA : (sp6ToSL6 (F := F)).range ⊔ sl6BlockA F = ⊤ := by
  set H := (sp6ToSL6 (F := F)).range ⊔ sl6BlockA F with hH
  have hB : ∀ i j : Fin 6, i ∈ sl6BlockAIdx → j ∈ sl6BlockAIdx → SL6TrIn H i j :=
    fun i j hi hj h c => mem_sup_right (transvection_mem_sl6BlockA h hi hj c)
  have h03 : SL6TrIn H 0 3 := fun h c => mem_sup_left (transvection_mem_range_sp6ToSL6 h rfl c)
  have h30 : SL6TrIn H 3 0 := fun h c => mem_sup_left (transvection_mem_range_sp6ToSL6 h rfl c)
  have h02 : SL6TrIn H 0 2 := by
    intro h c
    have hu := transvection_mul_mem_range_sp6ToSL6 (F := F) (i := 0) (j := 1) (i' := 4) (j' := 3)
      (by decide) (by decide) rfl rfl (by decide) (by decide) c
    have hx := transvection_mem_sl6BlockA (F := F) (i := 1) (j := 2) (by decide) (by decide)
      (by decide) 1
    have hc := slTransvection_commute (n := 6) (F := F) (i := 4) (j := 3) (k := 1) (l := 2)
      (by decide) (by decide) (by decide) (by decide) c 1
    have hf := slTransvection_commutator_formula (n := 6) (F := F) (i := 0) (j := 1) (k := 2)
      (by decide) (by decide) h c 1
    rw [mul_one] at hf
    set a := SpecialLinearGroup.transvection (F := F) (show (0 : Fin 6) ≠ 1 by decide) c
    set b := SpecialLinearGroup.transvection (F := F) (show (4 : Fin 6) ≠ 3 by decide) c
    set x := SpecialLinearGroup.transvection (F := F) (show (1 : Fin 6) ≠ 2 by decide) 1
    have key : a * b * x * (a * b)⁻¹ * x⁻¹ = a * x * a⁻¹ * x⁻¹ := by
      calc a * b * x * (a * b)⁻¹ * x⁻¹ = a * (b * x) * b⁻¹ * a⁻¹ * x⁻¹ := by group
        _ = a * (x * b) * b⁻¹ * a⁻¹ * x⁻¹ := by rw [hc]
        _ = a * x * a⁻¹ * x⁻¹ := by group
    rw [← hf, ← key]
    exact mul_mem (mul_mem (mul_mem (mem_sup_left hu) (mem_sup_right hx))
      (inv_mem (mem_sup_left hu))) (inv_mem (mem_sup_right hx))
  have h20 : SL6TrIn H 2 0 := by
    intro h c
    have hu := transvection_mul_mem_range_sp6ToSL6 (F := F) (i := 1) (j := 0) (i' := 3) (j' := 4)
      (by decide) (by decide) rfl rfl (by decide) (by decide) c
    have hx := transvection_mem_sl6BlockA (F := F) (i := 2) (j := 1) (by decide) (by decide)
      (by decide) 1
    have hc := slTransvection_commute (n := 6) (F := F) (i := 2) (j := 1) (k := 3) (l := 4)
      (by decide) (by decide) (by decide) (by decide) 1 c
    have hf := slTransvection_commutator_formula (n := 6) (F := F) (i := 2) (j := 1) (k := 0)
      (by decide) (by decide) h 1 c
    rw [one_mul] at hf
    set a := SpecialLinearGroup.transvection (F := F) (show (1 : Fin 6) ≠ 0 by decide) c
    set b := SpecialLinearGroup.transvection (F := F) (show (3 : Fin 6) ≠ 4 by decide) c
    set x := SpecialLinearGroup.transvection (F := F) (show (2 : Fin 6) ≠ 1 by decide) 1
    have key : x * (a * b) * x⁻¹ * (a * b)⁻¹ = x * a * x⁻¹ * a⁻¹ := by
      calc x * (a * b) * x⁻¹ * (a * b)⁻¹ = x * a * x⁻¹ * (x * b) * x⁻¹ * b⁻¹ * a⁻¹ := by group
        _ = x * a * x⁻¹ * (b * x) * x⁻¹ * b⁻¹ * a⁻¹ := by rw [hc]
        _ = x * a * x⁻¹ * a⁻¹ := by group
    rw [← hf, ← key]
    exact mul_mem (mul_mem (mul_mem (mem_sup_right hx) (mem_sup_left hu))
      (inv_mem (mem_sup_right hx))) (inv_mem (mem_sup_left hu))
  have h0 : ∀ j : Fin 6, (0 : Fin 6) ≠ j → SL6TrIn H 0 j := by
    intro j hj
    by_cases hj2 : j = 2
    · subst hj2; exact h02
    by_cases hj3 : j = 3
    · subst hj3; exact h03
    have hjI : j ∈ sl6BlockAIdx := by revert j; decide
    exact h02.trans (hB 2 j (by decide) hjI) (by decide) (Ne.symm hj2)
  have hc0 : ∀ i : Fin 6, i ∈ sl6BlockAIdx → SL6TrIn H i 0 := by
    intro i hi
    by_cases hi2 : i = 2
    · subst hi2; exact h20
    exact (hB i 2 hi (by decide)).trans h20 hi2 (by decide)
  have h3 : ∀ j : Fin 6, (3 : Fin 6) ≠ j → SL6TrIn H 3 j := by
    intro j hj
    by_cases hj0 : j = 0
    · subst hj0; exact h30
    exact h30.trans (h0 j (Ne.symm hj0)) (by decide) (Ne.symm hj0)
  have hc3 : ∀ i : Fin 6, i ∈ sl6BlockAIdx → SL6TrIn H i 3 := by
    intro i hi
    have hi0 : i ≠ 0 := by revert i; decide
    exact (hc0 i hi).trans h03 hi0 (by decide)
  have hI : ∀ x : Fin 6, x ≠ 0 → x ≠ 3 → x ∈ sl6BlockAIdx := by decide
  have hall : ∀ i j : Fin 6, i ≠ j → SL6TrIn H i j := by
    intro i j hij
    by_cases hi0 : i = 0
    · subst hi0; exact h0 j hij
    by_cases hi3 : i = 3
    · subst hi3; exact h3 j hij
    have hiI : i ∈ sl6BlockAIdx := hI i hi0 hi3
    by_cases hj0 : j = 0
    · subst hj0; exact hc0 i hiI
    by_cases hj3 : j = 3
    · subst hj3; exact hc3 i hiI
    exact hB i j hiI (hI j hj0 hj3)
  refine eq_top_iff.2 ?_
  rw [← SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field, closure_le]
  rintro _ ⟨t, rfl⟩
  exact hall t.i t.j t.hij t.hij t.c

end Generation

end CFSG.SeitzReduction.F4Pilot
