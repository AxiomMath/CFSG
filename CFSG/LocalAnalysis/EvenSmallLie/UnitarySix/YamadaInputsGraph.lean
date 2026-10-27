module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearPureGraph
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInputsLift

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaInputs

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
open scoped MatrixGroups

section Fixed

variable {n : ℕ} {F : Type} [Field F]

theorem stdSL_one_one_coe (C : GL (Fin n) F) (x : SL(n, F)) :
    ((stdSL n F C 1 1 x : SL(n, F)) : Matrix (Fin n) (Fin n) F) =
      C.val * ((x⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F)ᵀ * (C⁻¹).val := by
  rw [stdSL, map_one, mul_one, pow_one, MulAut.mul_apply,
    CatalogueBHigherLinearAction.slConjugation_matrix, CatalogueBGraphForm.slGraphAut_matrix]

theorem stdSL_one_one_eq_self (C : GL (Fin n) F) {x : SL(n, F)}
    (hx : (x : Matrix (Fin n) (Fin n) F)ᵀ * (C⁻¹).val * x = (C⁻¹).val) :
    stdSL n F C 1 1 x = x := by
  apply Subtype.ext
  rw [stdSL_one_one_coe]
  have hXY : (x : Matrix (Fin n) (Fin n) F) * ((x⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F) =
      1 := by
    exact congrArg (fun g : SL(n, F) => (g : Matrix (Fin n) (Fin n) F)) (mul_inv_cancel x)
  have hcd : C.val * (C⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc C.val * ((x⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F)ᵀ * (C⁻¹).val
      = C.val * ((x⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F)ᵀ *
          ((x : Matrix (Fin n) (Fin n) F)ᵀ * (C⁻¹).val * x) := by rw [hx]
    _ = C.val * ((x : Matrix (Fin n) (Fin n) F) *
          ((x⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F))ᵀ * (C⁻¹).val * x := by
        rw [transpose_mul]
        simp only [Matrix.mul_assoc]
    _ = x := by rw [hXY, transpose_one, Matrix.mul_one, hcd, Matrix.one_mul]

theorem transpose_mul_mul_slConjugation (C P : GL (Fin n) F) {y : SL(n, F)}
    (hy : (y : Matrix (Fin n) (Fin n) F)ᵀ * (P.valᵀ * (C⁻¹).val * P.val) * y =
      P.valᵀ * (C⁻¹).val * P.val) :
    ((CatalogueBHigherLinearAction.slConjugation n F P y : SL(n, F)) :
        Matrix (Fin n) (Fin n) F)ᵀ * (C⁻¹).val *
      (CatalogueBHigherLinearAction.slConjugation n F P y : SL(n, F)) = (C⁻¹).val := by
  rw [CatalogueBHigherLinearAction.slConjugation_matrix, transpose_mul, transpose_mul]
  have hP : P.val * (P⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc (P⁻¹).valᵀ * ((y : Matrix (Fin n) (Fin n) F)ᵀ * P.valᵀ) * (C⁻¹).val *
        (P.val * y * (P⁻¹).val)
      = (P⁻¹).valᵀ * ((y : Matrix (Fin n) (Fin n) F)ᵀ * (P.valᵀ * (C⁻¹).val * P.val) * y) *
          (P⁻¹).val := by
        simp only [Matrix.mul_assoc]
    _ = (P.val * (P⁻¹).val)ᵀ * (C⁻¹).val * (P.val * (P⁻¹).val) := by
        rw [hy, transpose_mul]
        simp only [Matrix.mul_assoc]
    _ = (C⁻¹).val := by rw [hP, transpose_one, Matrix.one_mul, Matrix.mul_one]

end Fixed

section Unipotent

variable {n r : ℕ} {F : Type} [Field F]

def graphSumEquiv (h : r + r = n) : Fin r ⊕ Fin r ≃ Fin n :=
  finSumFinEquiv.trans (finCongr h)

theorem val_graphSumEquiv_inl (h : r + r = n) (i : Fin r) :
    ((graphSumEquiv h (.inl i) : Fin n) : ℕ) = i := by
  simp [graphSumEquiv]

theorem val_graphSumEquiv_inr (h : r + r = n) (i : Fin r) :
    ((graphSumEquiv h (.inr i) : Fin n) : ℕ) = r + i := by
  simp only [graphSumEquiv, Equiv.trans_apply, finSumFinEquiv_apply_right, finCongr_apply,
    Fin.val_cast, Fin.val_natAdd]

theorem det_coe_unipotent (u : SymplecticFlag.unipotent r F) :
    (((u : StatedSp r F) : GL (Fin r ⊕ Fin r) F) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F).det = 1 := by
  obtain ⟨A, C, hA, -, hu⟩ := u.2
  rw [hu, SymplecticFlag.blockMat, det_fromBlocks_zero₂₁, det_transpose, det_nonsing_inv,
    hA.det_eq_one, Ring.inverse_one, mul_one]

noncomputable def graphUnipotentHom (h : r + r = n) :
    SymplecticFlag.unipotent r F →* SL(n, F) where
  toFun u := ⟨reindex (graphSumEquiv h) (graphSumEquiv h)
    (((u : StatedSp r F) : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F),
    by rw [det_reindex_self, det_coe_unipotent]⟩
  map_one' := by
    apply Subtype.ext
    exact (reindexRingEquiv F (graphSumEquiv h)).map_one
  map_mul' u v := by
    apply Subtype.ext
    exact (reindexRingEquiv F (graphSumEquiv h)).map_mul _ _

theorem coe_graphUnipotentHom (h : r + r = n) (u : SymplecticFlag.unipotent r F) :
    ((graphUnipotentHom h u : SL(n, F)) : Matrix (Fin n) (Fin n) F) =
      reindex (graphSumEquiv h) (graphSumEquiv h)
        (((u : StatedSp r F) : GL (Fin r ⊕ Fin r) F) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) := by
  simp only [graphUnipotentHom]
  rfl

theorem graphUnipotentHom_injective (h : r + r = n) :
    Function.Injective (graphUnipotentHom (F := F) h) := by
  intro u v huv
  have huv' := congrArg (fun x : SL(n, F) => (x : Matrix (Fin n) (Fin n) F)) huv
  simp only [coe_graphUnipotentHom] at huv'
  exact Subtype.ext (Subtype.ext (Units.ext ((reindex _ _).injective huv')))

theorem transpose_reindex_mul_mul {m : Type} [Fintype m] [DecidableEq m]
    (e : Fin r ⊕ Fin r ≃ m) {M G : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F}
    (hM : Mᵀ * G * M = G) : (reindex e e M)ᵀ * reindex e e G * reindex e e M = reindex e e G := by
  rw [transpose_reindex, ← coe_reindexRingEquiv F e, ← map_mul, ← map_mul, hM]

end Unipotent

section Forms

variable {n r : ℕ} {F : Type} [Field F]

theorem transpose_mul_swap_mul_unipotent [CharP F 2] (u : SymplecticFlag.unipotent r F) :
    (((u : StatedSp r F) : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)ᵀ *
        fromBlocks 0 1 1 0 * ((u : StatedSp r F) : GL (Fin r ⊕ Fin r) F).val =
      (fromBlocks 0 1 1 0 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) := by
  have h := SymplecticTorusWeyl.mem_statedSp_iff.mp (u : StatedSp r F).2
  have hneg : (-1 : Matrix (Fin r) (Fin r) F) = 1 := by
    rw [neg_eq_iff_add_eq_zero, ← two_smul F, CharTwo.two_eq_zero, zero_smul]
  rwa [hneg] at h

theorem coe_unipotent_inr_zero_apply (hr : 0 < r) (u : SymplecticFlag.unipotent r F)
    (x : Fin r ⊕ Fin r) :
    (((u : StatedSp r F) : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)
      (.inr ⟨0, hr⟩) x = if x = .inr ⟨0, hr⟩ then 1 else 0 := by
  obtain ⟨A, C, hA, -, hu⟩ := u.2
  rw [hu, SymplecticFlag.blockMat]
  rcases x with j | j
  · simp
  · rw [fromBlocks_apply₂₂, transpose_apply]
    by_cases hj : j = ⟨0, hr⟩
    · subst hj
      rw [hA.inv.2, ite_eq_left rfl]
    · rw [ite_eq_right (by simpa using hj)]
      exact hA.inv.1 (show (⟨0, hr⟩ : Fin r) < j from
        Fin.lt_def.2 (Nat.pos_of_ne_zero fun h0 => hj (Fin.ext h0)))

theorem single_mul_unipotent (hr : 0 < r) (u : SymplecticFlag.unipotent r F) :
    single (Sum.inr ⟨0, hr⟩ : Fin r ⊕ Fin r) (.inr ⟨0, hr⟩) (1 : F) *
        (((u : StatedSp r F) : GL (Fin r ⊕ Fin r) F) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) =
      single (.inr ⟨0, hr⟩) (.inr ⟨0, hr⟩) 1 := by
  ext i j
  by_cases hi : i = .inr ⟨0, hr⟩
  · subst hi
    rw [single_mul_apply_same, one_mul, coe_unipotent_inr_zero_apply, single_apply]
    simp [eq_comm]
  · rw [single_mul_apply_of_ne (h := hi), single_apply_of_row_ne (Ne.symm hi)]

theorem transpose_mul_single_mul_unipotent (hr : 0 < r) (u : SymplecticFlag.unipotent r F) :
    (((u : StatedSp r F) : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)ᵀ *
        single (Sum.inr ⟨0, hr⟩ : Fin r ⊕ Fin r) (.inr ⟨0, hr⟩) (1 : F) *
        ((u : StatedSp r F) : GL (Fin r ⊕ Fin r) F).val =
      single (.inr ⟨0, hr⟩) (.inr ⟨0, hr⟩) (1 : F) := by
  have h1 := single_mul_unipotent hr u
  have h2 : (((u : StatedSp r F) : GL (Fin r ⊕ Fin r) F) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)ᵀ * single (.inr ⟨0, hr⟩) (.inr ⟨0, hr⟩) 1 =
      single (.inr ⟨0, hr⟩) (.inr ⟨0, hr⟩) (1 : F) := by
    calc _ = (single (Sum.inr ⟨0, hr⟩ : Fin r ⊕ Fin r) (.inr ⟨0, hr⟩) (1 : F) *
          ((u : StatedSp r F) : GL (Fin r ⊕ Fin r) F).val)ᵀ := by
          rw [transpose_mul, transpose_single]
      _ = _ := by rw [h1, transpose_single]
  rw [h2, h1]

theorem transpose_mul_swap_add_single_mul_unipotent [CharP F 2] (hr : 0 < r)
    (u : SymplecticFlag.unipotent r F) :
    (((u : StatedSp r F) : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)ᵀ *
        (fromBlocks 0 1 1 0 + single (Sum.inr ⟨0, hr⟩ : Fin r ⊕ Fin r) (.inr ⟨0, hr⟩) 1) *
        ((u : StatedSp r F) : GL (Fin r ⊕ Fin r) F).val =
      (fromBlocks 0 1 1 0 + single (.inr ⟨0, hr⟩) (.inr ⟨0, hr⟩) 1 :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) := by
  rw [Matrix.mul_add, Matrix.add_mul, transpose_mul_swap_mul_unipotent,
    transpose_mul_single_mul_unipotent]

theorem reindex_fromBlocks_swap (h : r + r = n) :
    reindex (graphSumEquiv h) (graphSumEquiv h)
      (fromBlocks 0 1 1 0 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) = blockSwapJ n r := by
  ext i j
  obtain ⟨a, rfl⟩ := (graphSumEquiv h).surjective i
  obtain ⟨b, rfl⟩ := (graphSumEquiv h).surjective j
  rw [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    blockSwapJ, of_apply]
  rcases a with a | a <;> rcases b with b | b <;>
  · have ha := a.isLt
    have hb := b.isLt
    simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, one_apply, val_graphSumEquiv_inl, val_graphSumEquiv_inr, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)

theorem reindex_single_inr (h : r + r = n) (hr : 0 < r) :
    reindex (graphSumEquiv h) (graphSumEquiv h)
        (single (Sum.inr ⟨0, hr⟩ : Fin r ⊕ Fin r) (.inr ⟨0, hr⟩) (1 : F)) =
      single (graphSumEquiv h (.inr ⟨0, hr⟩)) (graphSumEquiv h (.inr ⟨0, hr⟩)) 1 := by
  rw [reindex_apply, submatrix_single_equiv, Equiv.symm_symm]

theorem blockSwapJ_mul_blockSwapJ (h : r + r = n) :
    blockSwapJ n r * blockSwapJ n r = (1 : Matrix (Fin n) (Fin n) F) := by
  rw [← reindex_fromBlocks_swap h, ← coe_reindexRingEquiv F, ← map_mul, fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, zero_add, add_zero, fromBlocks_one,
    map_one]

end Forms

section Subgroup

variable {n r : ℕ} {F : Type} [Field F]

theorem exists_twoSubgroup_fixed_of_form [Finite F] [CharP F 2] (h : r + r = n)
    (C P : GL (Fin n) F) (G : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)
    (hG : P.valᵀ * (C⁻¹).val * P.val = reindex (graphSumEquiv h) (graphSumEquiv h) G)
    (hU : ∀ u : SymplecticFlag.unipotent r F,
      (((u : StatedSp r F) : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)ᵀ *
        G * ((u : StatedSp r F) : GL (Fin r ⊕ Fin r) F).val = G) :
    ∃ Q : Subgroup (SpecialLinearGroup (Fin n) F), (∀ x ∈ Q, stdSL n F C 1 1 x = x) ∧
      IsPGroup 2 Q ∧ Nat.card F ^ (r * r) ≤ Nat.card Q := by
  set φ := (CatalogueBHigherLinearAction.slConjugation n F P).toMonoidHom.comp
    (graphUnipotentHom (F := F) h)
  have hinj : Function.Injective φ := fun a b hab =>
    graphUnipotentHom_injective h ((CatalogueBHigherLinearAction.slConjugation n F P).injective hab)
  have hcard : Nat.card φ.range = Nat.card F ^ (r * r) := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, SymplecticFlag.card_unipotent, sq]
  refine ⟨φ.range, ?_, ?_, hcard.ge⟩
  · rintro x ⟨u, rfl⟩
    refine stdSL_one_one_eq_self C (transpose_mul_mul_slConjugation C P ?_)
    rw [hG, coe_graphUnipotentHom]
    exact transpose_reindex_mul_mul _ (hU u)
  · have := Fintype.ofFinite F
    obtain ⟨k, -, hk⟩ := FiniteField.card F 2
    rw [← Nat.card_eq_fintype_card] at hk
    exact IsPGroup.of_card (n := k * (r * r)) (by rw [hcard, hk, ← pow_mul])

theorem exists_twoSubgroup_fixed_blockSwapJ [Finite F] [CharP F 2] (h : r + r = n)
    (C : GL (Fin n) F) (hC : (C : Matrix (Fin n) (Fin n) F) = blockSwapJ n r) :
    ∃ Q : Subgroup (SpecialLinearGroup (Fin n) F), (∀ x ∈ Q, stdSL n F C 1 1 x = x) ∧
      IsPGroup 2 Q ∧ Nat.card F ^ (r * r) ≤ Nat.card Q := by
  refine exists_twoSubgroup_fixed_of_form h C 1 (fromBlocks 0 1 1 0) ?_
    transpose_mul_swap_mul_unipotent
  have hCC : (C⁻¹).val = C.val := by
    calc (C⁻¹).val = (C⁻¹).val * (C.val * C.val) := by
          rw [hC, blockSwapJ_mul_blockSwapJ h, Matrix.mul_one]
      _ = C.val := by
          rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  rw [Units.val_one, transpose_one, Matrix.one_mul, Matrix.mul_one, hCC, hC,
    reindex_fromBlocks_swap]

theorem exists_twoSubgroup_fixed_one [Finite F] [CharP F 2] (h : r + r = n) (hr : 0 < r)
    (P : GL (Fin n) F) (i : Fin n) (hi : (i : ℕ) = r)
    (hP : P.valᵀ * P.val = blockSwapJ n r + single i i 1) :
    ∃ Q : Subgroup (SpecialLinearGroup (Fin n) F), (∀ x ∈ Q, stdSL n F 1 1 1 x = x) ∧
      IsPGroup 2 Q ∧ Nat.card F ^ (r * r) ≤ Nat.card Q := by
  refine exists_twoSubgroup_fixed_of_form h 1 P
    (fromBlocks 0 1 1 0 + single (.inr ⟨0, hr⟩) (.inr ⟨0, hr⟩) 1) ?_ ?_
  swap
  · intro u
    exact transpose_mul_swap_add_single_mul_unipotent hr u
  have hi' : graphSumEquiv h (.inr ⟨0, hr⟩) = i :=
    Fin.ext (by rw [val_graphSumEquiv_inr, hi]; rfl)
  rw [inv_one, Units.val_one, Matrix.mul_one, hP, ← coe_reindexRingEquiv F, map_add,
    coe_reindexRingEquiv, reindex_fromBlocks_swap, reindex_single_inr h hr, hi']

end Subgroup

section Matrices

variable (F : Type) [Field F]

def graphP4 : Matrix (Fin 4) (Fin 4) F :=
  !![1, 0, 0, 1; 1, 0, 1, 0; 1, 1, 0, 0; 1, 1, 0, 1]

def graphP4Inv : Matrix (Fin 4) (Fin 4) F :=
  !![1, 0, 1, 1; 1, 0, 0, 1; 1, 1, 1, 1; 0, 0, 1, 1]

variable {F}

theorem graphP4Inv_mul [CharP F 2] : graphP4Inv F * graphP4 F = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [graphP4, graphP4Inv, mul_apply, Fin.sum_univ_four, one_apply, CharTwo.add_self_eq_zero]

theorem transpose_graphP4_mul [CharP F 2] :
    (graphP4 F)ᵀ * graphP4 F = blockSwapJ 4 2 + single 2 2 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [graphP4, mul_apply, Fin.sum_univ_four, blockSwapJ, CharTwo.add_self_eq_zero]

variable (F) in
def graphP6 : Matrix (Fin 6) (Fin 6) F :=
  !![1, 0, 0, 0, 1, 1; 1, 0, 0, 1, 0, 0; 1, 0, 1, 0, 0, 0; 1, 0, 1, 0, 0, 1;
    1, 1, 0, 0, 0, 1; 1, 1, 0, 0, 1, 1]

variable (F) in
def graphP6Inv : Matrix (Fin 6) (Fin 6) F :=
  !![1, 0, 1, 1, 1, 1; 1, 0, 0, 0, 0, 1; 1, 0, 0, 1, 1, 1; 1, 1, 1, 1, 1, 1;
    0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 0, 0]

theorem graphP6Inv_mul [CharP F 2] : graphP6Inv F * graphP6 F = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [graphP6, graphP6Inv, mul_apply, Fin.sum_univ_six, one_apply, CharTwo.add_self_eq_zero]

theorem transpose_graphP6_mul [CharP F 2] :
    (graphP6 F)ᵀ * graphP6 F = blockSwapJ 6 3 + single 3 3 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [graphP6, mul_apply, Fin.sum_univ_six, blockSwapJ, CharTwo.add_self_eq_zero]

end Matrices

theorem exists_twoSubgroup_fixed_graph {F : Type} [Field F] [Finite F] [CharP F 2] {n r : ℕ}
    (hr : r = 2 ∨ r = 3) (hn : n = 2 * r) (C : GL (Fin n) F)
    (hC : (C : Matrix (Fin n) (Fin n) F) = 1 ∨
      ∃ r', n = 2 * r' ∧ (C : Matrix (Fin n) (Fin n) F) = blockSwapJ n r') :
    ∃ Q : Subgroup (SpecialLinearGroup (Fin n) F), (∀ x ∈ Q, stdSL n F C 1 1 x = x) ∧
      IsPGroup 2 Q ∧ Nat.card F ^ (r * r) ≤ Nat.card Q := by
  rcases hC with hC | ⟨r', hr', hC⟩
  · obtain rfl : C = 1 := Units.ext hC
    rcases hr with rfl | rfl
    · obtain rfl : n = 4 := hn
      exact exists_twoSubgroup_fixed_one (by norm_num) (by norm_num)
        ⟨graphP4 F, graphP4Inv F, mul_eq_one_comm.mp graphP4Inv_mul, graphP4Inv_mul⟩ 2 rfl
        transpose_graphP4_mul
    · obtain rfl : n = 6 := hn
      exact exists_twoSubgroup_fixed_one (by norm_num) (by norm_num)
        ⟨graphP6 F, graphP6Inv F, mul_eq_one_comm.mp graphP6Inv_mul, graphP6Inv_mul⟩ 3 rfl
        transpose_graphP6_mul
  · obtain rfl : r' = r := by omega
    exact exists_twoSubgroup_fixed_blockSwapJ (by omega) C hC

end CFSG.EvenSmallLie.UnitarySix.YamadaInputs
