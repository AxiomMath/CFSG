module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvConj
public import CFSG.GH74.GLS.IVK.Proofs2.NoOuter
public import CFSG.GH74.GLS.IVK.Proofs2.TwoTori
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Local.Prop27Cfg
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SurvU4Core
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvDefs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

namespace U4C1

open Subgroup Matrix Module CFSG CFSG.Blueprint CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped MatrixGroups commutatorElement

section Model

variable {p f : ℕ} {K : Type} [Field K]

@[expose] def hyp4 : HypIndex 2 0 ≃ Fin 4 where
  toFun a := match a with
    | .inl i => ⟨i.1, by omega⟩
    | .inr (.inl k) => k.elim0
    | .inr (.inr i) => ⟨2 + i.1, by omega⟩
  invFun j := if hj : j.1 < 2 then .inl ⟨j.1, hj⟩ else .inr (.inr ⟨j.1 - 2, by omega⟩)
  left_inv a := by
    rcases a with ⟨i, hi⟩ | k | ⟨i, hi⟩
    · simp [hi]
    · exact k.elim0
    · have h1 : ¬ (2 + i < 2) := by omega
      simp [h1]
  right_inv j := by
    obtain ⟨j, hj⟩ := j
    by_cases h2 : j < 2
    · simp [h2]
    · have h3 : 2 + (j - 2) = j := by omega
      simp [h2, h3]

@[expose] def toHyp (X : Matrix (Fin 4) (Fin 4) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K :=
  X.submatrix hyp4 hyp4

@[expose] def fromHyp (M : Matrix (HypIndex 2 0) (HypIndex 2 0) K) : Matrix (Fin 4) (Fin 4) K :=
  M.submatrix hyp4.symm hyp4.symm

omit [Field K] in
theorem toHyp_apply (X : Matrix (Fin 4) (Fin 4) K) (a b : HypIndex 2 0) :
    toHyp X a b = X (hyp4 a) (hyp4 b) := rfl

omit [Field K] in
theorem fromHyp_toHyp (X : Matrix (Fin 4) (Fin 4) K) : fromHyp (toHyp X) = X := by
  ext i j
  simp [fromHyp, toHyp]

omit [Field K] in
theorem toHyp_fromHyp (M : Matrix (HypIndex 2 0) (HypIndex 2 0) K) : toHyp (fromHyp M) = M := by
  ext a b
  simp [fromHyp, toHyp]

theorem toHyp_mul (X Y : Matrix (Fin 4) (Fin 4) K) : toHyp (X * Y) = toHyp X * toHyp Y := by
  simp [toHyp, Matrix.submatrix_mul_equiv]

theorem toHyp_one : toHyp (1 : Matrix (Fin 4) (Fin 4) K) = 1 := by
  simp [toHyp]

theorem det_toHyp (X : Matrix (Fin 4) (Fin 4) K) : (toHyp X).det = X.det := by
  simp [toHyp, Matrix.det_submatrix_equiv_self]

@[expose] def J4 : Matrix (Fin 4) (Fin 4) K := !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

theorem toHyp_J4 : toHyp (J4 : Matrix (Fin 4) (Fin 4) K) = hypGram 2 0 K := by
  ext a b
  rw [hypGram_apply]
  rcases a with i | k | i <;> rcases b with j | l | j <;>
    first
    | exact k.elim0
    | exact l.elim0
    | (fin_cases i <;> fin_cases j <;> simp [toHyp_apply, hyp4, J4])

theorem toHyp_mulVec (X : Matrix (Fin 4) (Fin 4) K) (u : Fin 4 → K) :
    toHyp X *ᵥ (u ∘ hyp4) = (X *ᵥ u) ∘ hyp4 := by
  have := Matrix.submatrix_mulVec_equiv X (u ∘ hyp4) hyp4 hyp4
  rw [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] at this
  exact this

section Unitary

variable (h : UnitaryFieldData p f K)

@[expose] def IsU4 (X : Matrix (Fin 4) (Fin 4) K) : Prop :=
  (X.map h.bar)ᵀ * J4 * X = J4 ∧ X.det = 1

variable {h}

theorem IsU4.mul {X Y : Matrix (Fin 4) (Fin 4) K} (hX : IsU4 h X) (hY : IsU4 h Y) :
    IsU4 h (X * Y) := by
  refine ⟨?_, by rw [det_mul, hX.2, hY.2, one_mul]⟩
  rw [Matrix.map_mul, transpose_mul]
  calc (Y.map h.bar)ᵀ * (X.map h.bar)ᵀ * J4 * (X * Y)
      = (Y.map h.bar)ᵀ * ((X.map h.bar)ᵀ * J4 * X) * Y := by simp only [Matrix.mul_assoc]
    _ = J4 := by rw [hX.1, hY.1]

theorem isU4_one : IsU4 h (1 : Matrix (Fin 4) (Fin 4) K) := by
  refine ⟨?_, det_one⟩
  simp [Matrix.map_one]

@[expose] noncomputable def hypOf (X : Matrix (Fin 4) (Fin 4) K) (hX : IsU4 h X) : hypSU h 2 0 :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (toHyp X) (by rw [det_toHyp, hX.2]; exact one_ne_zero), by
    rw [mem_hypSU, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    refine ⟨?_, by rw [det_toHyp, hX.2]⟩
    rw [← toHyp_J4]
    have e : ((toHyp X).map h.bar)ᵀ = toHyp ((X.map h.bar)ᵀ) := by
      ext a b
      simp [toHyp]
    rw [e, ← toHyp_mul, ← toHyp_mul, hX.1]⟩

theorem coe_hypOf (X : Matrix (Fin 4) (Fin 4) K) (hX : IsU4 h X) :
    (((hypOf X hX : hypSU h 2 0) : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
      toHyp X :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

theorem hypOf_mul {X Y : Matrix (Fin 4) (Fin 4) K} (hX : IsU4 h X) (hY : IsU4 h Y) :
    hypOf (X * Y) (hX.mul hY) = hypOf X hX * hypOf Y hY := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Units.val_mul, coe_hypOf, coe_hypOf, coe_hypOf, toHyp_mul]

theorem hypOf_ext {X Y : Matrix (Fin 4) (Fin 4) K} (hX : IsU4 h X) (hY : IsU4 h Y) (hXY : X = Y) :
    hypOf X hX = hypOf Y hY := by
  subst hXY
  rfl

end Unitary

section Elements

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

@[expose] def u4A0 : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1]

@[expose] def u4Sw : Matrix (Fin 4) (Fin 4) K :=
  !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]

@[expose] def u4U (c : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, c, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def u4L (c : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; 0, 1, 0, 0; c, 0, 1, 0; 0, 0, 0, 1]

@[expose] noncomputable def u4T (l : K) : Matrix (Fin 4) (Fin 4) K :=
  !![l, 0, 0, 0; 0, h.bar l, 0, 0; 0, 0, -l, 0; 0, 0, 0, -h.bar l]

local macro "u4_norm" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| (
    simp only [u4A0, u4Sw, u4U, u4L, u4T, J4, Matrix.map_apply, Matrix.transpose_apply,
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val,
      Matrix.neg_apply, Matrix.one_apply, Fin.isValue, Fin.reduceFinMk, Fin.zero_eta, Fin.mk_one,
      map_zero, map_one, map_neg, map_add, map_mul, h.bar_bar, mul_zero, zero_mul, mul_one,
      one_mul, add_zero, zero_add, neg_zero, Fin.reduceEq, ite_true, ite_false, neg_mul,
      mul_neg, neg_neg] $[$loc]?))

theorem isU4_A0 : IsU4 h (u4A0 : Matrix (Fin 4) (Fin 4) K) := by
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> u4_norm
  · rw [Matrix.det_succ_row_zero]
    simp [u4A0, Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]

theorem isU4_Sw : IsU4 h (u4Sw : Matrix (Fin 4) (Fin 4) K) := by
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> u4_norm
  · rw [Matrix.det_succ_row_zero]
    simp [u4Sw, Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]

theorem isU4_U {c : K} (hc : h.bar c = -c) : IsU4 h (u4U c : Matrix (Fin 4) (Fin 4) K) := by
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> u4_norm
    all_goals simp [hc]
  · rw [Matrix.det_succ_row_zero]
    simp [u4U, Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]

theorem isU4_L {c : K} (hc : h.bar c = -c) : IsU4 h (u4L c : Matrix (Fin 4) (Fin 4) K) := by
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> u4_norm
    all_goals simp [hc]
  · rw [Matrix.det_succ_row_zero]
    simp [u4L, Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]

theorem isU4_T {l : K} (hl : h.norm l = -1) : IsU4 h (u4T h l : Matrix (Fin 4) (Fin 4) K) := by
  have hl' : l * h.bar l = -1 := hl
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> u4_norm <;> linear_combination (-1 : K) * hl'
  · rw [Matrix.det_succ_row_zero]
    simp [u4T, Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]
    linear_combination (l * h.bar l - 1) * hl'

theorem isU4_neg : IsU4 h (-1 : Matrix (Fin 4) (Fin 4) K) := by
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> u4_norm
  · simp [Matrix.det_neg]
    norm_num

end Elements

end Model

end U4C1

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
