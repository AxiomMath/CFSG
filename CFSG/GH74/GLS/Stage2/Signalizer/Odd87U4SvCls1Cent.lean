module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvCls1Fix

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

namespace U4C1

open Subgroup Matrix Module CFSG CFSG.Blueprint CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped MatrixGroups commutatorElement

section Cent

variable {p f : ℕ} {K : Type} [Field K]

section CentStd

variable {p f : ℕ} {K : Type} [Field K]

@[expose] def u4Blk (τ a b c d : K) : Matrix (Fin 4) (Fin 4) K :=
  !![a, 0, τ⁻¹ * b, 0; 0, 1, 0, 0; τ * c, 0, d, 0; 0, 0, 0, 1]

theorem u4Blk_mul {τ : K} (hτ0 : τ ≠ 0) (a b c d a' b' c' d' : K) :
    u4Blk τ a b c d * u4Blk τ a' b' c' d' =
      u4Blk τ (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [u4Blk, Matrix.mul_apply, Fin.sum_univ_four] <;> field_simp

theorem u4Blk_one (τ : K) : u4Blk τ 1 0 0 1 = (1 : Matrix (Fin 4) (Fin 4) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u4Blk]

theorem isU4_blk (h : UnitaryFieldData p f K) {τ a b c d : K} (hτ0 : τ ≠ 0) (hτ : h.bar τ = -τ)
    (ha : h.bar a = a) (hb : h.bar b = b) (hc : h.bar c = c) (hd : h.bar d = d)
    (hdet : a * d - b * c = 1) : IsU4 h (u4Blk τ a b c d) := by
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [u4Blk, J4, Matrix.map_apply, Matrix.transpose_apply, Matrix.mul_apply, Fin.sum_univ_four,
        map_mul, map_inv₀, hτ, ha, hb, hc, hd] <;> field_simp <;>
      first | ring1 | linear_combination hdet
  · rw [Matrix.det_succ_row_zero]
    simp [u4Blk, Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]
    field_simp
    linear_combination hdet

end CentStd

section Iota

variable (h : UnitaryFieldData p f K)

theorem hypOf_one : hypOf (1 : Matrix (Fin 4) (Fin 4) K) (isU4_one (h := h)) = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_hypOf]
  simp [toHyp_one]

theorem sl2_entry_bar (S : SL(2, ↥h.fixedField)) (i j : Fin 2) :
    h.bar (((S : Matrix (Fin 2) (Fin 2) ↥h.fixedField) i j : ↥h.fixedField) : K) =
      (((S : Matrix (Fin 2) (Fin 2) ↥h.fixedField) i j : ↥h.fixedField) : K) :=
  h.mem_fixedField.1 ((S : Matrix (Fin 2) (Fin 2) ↥h.fixedField) i j).2

theorem sl2_det_coe (S : SL(2, ↥h.fixedField)) :
    (((S : Matrix (Fin 2) (Fin 2) ↥h.fixedField) 0 0 : ↥h.fixedField) : K) *
        (((S : Matrix (Fin 2) (Fin 2) ↥h.fixedField) 1 1 : ↥h.fixedField) : K) -
      (((S : Matrix (Fin 2) (Fin 2) ↥h.fixedField) 0 1 : ↥h.fixedField) : K) *
        (((S : Matrix (Fin 2) (Fin 2) ↥h.fixedField) 1 0 : ↥h.fixedField) : K) = 1 := by
  have := congrArg (Subtype.val : ↥h.fixedField → K) S.2
  rw [Matrix.det_fin_two] at this
  simpa using this

@[expose] def u4IotaMat (τ : K) (S : SL(2, ↥h.fixedField)) : Matrix (Fin 4) (Fin 4) K :=
  u4Blk τ (((S : Matrix (Fin 2) (Fin 2) ↥h.fixedField) 0 0 : ↥h.fixedField) : K)
    (((S : Matrix (Fin 2) (Fin 2) ↥h.fixedField) 0 1 : ↥h.fixedField) : K)
    (((S : Matrix (Fin 2) (Fin 2) ↥h.fixedField) 1 0 : ↥h.fixedField) : K)
    (((S : Matrix (Fin 2) (Fin 2) ↥h.fixedField) 1 1 : ↥h.fixedField) : K)

theorem isU4_iotaMat {τ : K} (hτ : h.bar τ = -τ) (hτ0 : τ ≠ 0) (S : SL(2, ↥h.fixedField)) :
    IsU4 h (u4IotaMat h τ S) :=
  isU4_blk h hτ0 hτ (sl2_entry_bar h S 0 0) (sl2_entry_bar h S 0 1) (sl2_entry_bar h S 1 0)
    (sl2_entry_bar h S 1 1) (sl2_det_coe h S)

@[expose] noncomputable def u4Iota {τ : K} (hτ : h.bar τ = -τ) (hτ0 : τ ≠ 0) :
    SL(2, ↥h.fixedField) →* hypSU h 2 0 where
  toFun S := hypOf (u4IotaMat h τ S) (isU4_iotaMat h hτ hτ0 S)
  map_one' := by
    rw [← hypOf_one h]
    refine hypOf_ext _ _ ?_
    simp [u4IotaMat, u4Blk_one]
  map_mul' S S' := by
    rw [← hypOf_mul]
    refine hypOf_ext _ _ ?_
    simp only [u4IotaMat]
    rw [u4Blk_mul hτ0]
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem coe_u4Iota {τ : K} (hτ : h.bar τ = -τ) (hτ0 : τ ≠ 0) (S : SL(2, ↥h.fixedField)) :
    (((u4Iota h hτ hτ0 S : hypSU h 2 0) : GL (HypIndex 2 0) K) :
      Matrix (HypIndex 2 0) (HypIndex 2 0) K) = toHyp (u4IotaMat h τ S) :=
  coe_hypOf _ (isU4_iotaMat h hτ hτ0 S)

end Iota

section CentFinal

variable {p f : ℕ} {K : Type} [Field K]

theorem fromHyp_mul (M N : Matrix (HypIndex 2 0) (HypIndex 2 0) K) :
    fromHyp (M * N) = fromHyp M * fromHyp N := by
  simp [fromHyp, Matrix.submatrix_mul_equiv]

theorem u4_cent4 {c c' : K} (hc : c ≠ 0) (hc' : c' ≠ 0) {X : Matrix (Fin 4) (Fin 4) K}
    (hU : X * u4U c = u4U c * X) (hL : X * u4L c' = u4L c' * X) :
    u4A0 * X = X * u4A0 := by
  have e12 := congrFun (congrFun hU 1) 2
  have e32 := congrFun (congrFun hU 3) 2
  have e01 := congrFun (congrFun hU 0) 1
  have e03 := congrFun (congrFun hU 0) 3
  have f10 := congrFun (congrFun hL 1) 0
  have f30 := congrFun (congrFun hL 3) 0
  have f21 := congrFun (congrFun hL 2) 1
  have f23 := congrFun (congrFun hL 2) 3
  simp [u4U, u4L, Matrix.mul_apply, Fin.sum_univ_four, hc, hc'] at e12 e32 e01 e03 f10 f30 f21 f23
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u4A0, Matrix.mul_apply, Fin.sum_univ_four, *]

theorem exists_traceZero_ne (h : UnitaryFieldData p f K) : ∃ τ : K, h.bar τ = -τ ∧ τ ≠ 0 := by
  obtain ⟨c, hc⟩ := h.exists_bar_ne
  exact ⟨c - h.bar c, by rw [map_sub, h.bar_bar]; ring, sub_ne_zero.2 (Ne.symm hc)⟩

theorem mem_fixSub_alpha0_of_comm_hyp (h : UnitaryFieldData p f K) (x : ↥(hypSU h 2 0))
    (hcomm : u4A0 * fromHyp ((x : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
      fromHyp ((x : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) * u4A0) :
    hypProj h 2 0 x ∈ fixSub (u4Alpha0 h) := by
  refine mem_fixSub_alpha0 h x 1 (one_mem _) ?_
  apply Units.ext
  simp only [u4A0El, Units.val_mul, Subgroup.coe_one, one_mul, coe_hypOf]
  have hx : ((x : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
      toHyp (fromHyp ((x : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K)) :=
    (toHyp_fromHyp _).symm
  rw [hx, ← toHyp_mul, ← toHyp_mul, hcomm]

theorem u4_cls1_cent_std (h : UnitaryFieldData p f K) (x : ↥(hypSU h 2 0))
    (hx : ∀ ι : SL(2, ↥h.fixedField) →* ↥(hypSU h 2 0),
      (∀ g, hypProj h 2 0 (ι g) ∈ fixSub (u4Alpha0 h)) → ∀ g, x * ι g = ι g * x) :
    u4Alpha0 h (hypProj h 2 0 x) = hypProj h 2 0 x := by
  obtain ⟨τ, hτ, hτ0⟩ := exists_traceZero_ne h
  have hfix : ∀ g, hypProj h 2 0 (u4Iota h hτ hτ0 g) ∈ fixSub (u4Alpha0 h) := fun g =>
    mem_fixSub_alpha0_of_comm h (isU4_iotaMat h hτ hτ0 g) (by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [u4A0, u4IotaMat, u4Blk, Matrix.mul_apply, Fin.sum_univ_four])
  have hc := hx _ hfix
  have hconv : ∀ g : SL(2, ↥h.fixedField), fromHyp ((x : GL (HypIndex 2 0) K) :
      Matrix (HypIndex 2 0) (HypIndex 2 0) K) * u4IotaMat h τ g =
      u4IotaMat h τ g * fromHyp ((x : GL (HypIndex 2 0) K) :
        Matrix (HypIndex 2 0) (HypIndex 2 0) K) := by
    intro g
    have h1 := congrArg (fun y : ↥(hypSU h 2 0) => fromHyp ((y : GL (HypIndex 2 0) K) :
      Matrix (HypIndex 2 0) (HypIndex 2 0) K)) (hc g)
    simp only [Subgroup.coe_mul, Units.val_mul, fromHyp_mul, coe_u4Iota, fromHyp_toHyp] at h1
    exact h1
  let u1 : SL(2, ↥h.fixedField) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  let l1 : SL(2, ↥h.fixedField) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  have hu1 : u4IotaMat h τ u1 = u4U τ⁻¹ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [u1, u4IotaMat, u4Blk, u4U]
  have hl1 : u4IotaMat h τ l1 = u4L τ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [l1, u4IotaMat, u4Blk, u4L]
  have hU := hconv u1
  have hL := hconv l1
  rw [hu1] at hU
  rw [hl1] at hL
  exact mem_fixSub.1 (mem_fixSub_alpha0_of_comm_hyp h x
    (u4_cent4 (inv_ne_zero hτ0) hτ0 hU hL))

end CentFinal

section Cent3Std

variable {p f : ℕ} {K : Type} [Field K]

theorem u4T_mul_U (h : UnitaryFieldData p f K) {l τ : K} (h3 : (3 : K) = 0) :
    u4T h l * u4U τ = u4U τ * u4U τ * u4T h l := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u4T, u4U, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals first | ring1 | linear_combination (l * τ) * h3

theorem u4T_mul_L (h : UnitaryFieldData p f K) {l τ : K} (h3 : (3 : K) = 0) :
    u4T h l * u4L τ = u4L τ * u4L τ * u4T h l := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u4T, u4L, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals first | ring1 | linear_combination (l * τ) * h3 | linear_combination (-(l * τ)) * h3

theorem u4_cls1_cent3_std (h : UnitaryFieldData p f K) (hq3 : p ^ f = 3) (x : ↥(hypSU h 2 0))
    (hc : ∀ a b : ↥(hypSU h 2 0), hypProj h 2 0 a ∈ fixSub (u4Alpha0 h) →
      hypProj h 2 0 b ∈ fixSub (u4Alpha0 h) → x * ⁅a, b⁆ = ⁅a, b⁆ * x) :
    u4Alpha0 h (hypProj h 2 0 x) = hypProj h 2 0 x := by
  obtain ⟨hp3, -⟩ := (Nat.Prime.pow_eq_iff Nat.prime_three).mp hq3
  have h3 : (3 : K) = 0 := by
    have hchar := h.charP
    subst hp3
    exact CharP.cast_eq_zero K 3
  obtain ⟨l, hl⟩ := OddUnitaryInvolutionSylow.exists_norm_eq_neg_one h
  obtain ⟨τ, hτ, hτ0⟩ := exists_traceZero_ne h
  have hTfix : hypProj h 2 0 (hypOf (u4T h l) (isU4_T h hl)) ∈ fixSub (u4Alpha0 h) :=
    mem_fixSub_alpha0_of_comm h (isU4_T h hl) (by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [u4A0, u4T, Matrix.mul_apply, Fin.sum_univ_four])
  have hUfix : hypProj h 2 0 (hypOf (u4U τ) (isU4_U h hτ)) ∈ fixSub (u4Alpha0 h) :=
    mem_fixSub_alpha0_of_comm h (isU4_U h hτ) (by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [u4A0, u4U, Matrix.mul_apply, Fin.sum_univ_four])
  have hLfix : hypProj h 2 0 (hypOf (u4L τ) (isU4_L h hτ)) ∈ fixSub (u4Alpha0 h) :=
    mem_fixSub_alpha0_of_comm h (isU4_L h hτ) (by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [u4A0, u4L, Matrix.mul_apply, Fin.sum_univ_four])
  have hTU : ⁅hypOf (u4T h l) (isU4_T h hl), hypOf (u4U τ) (isU4_U h hτ)⁆ =
      hypOf (u4U τ) (isU4_U h hτ) := by
    have hmul : hypOf (u4T h l) (isU4_T h hl) * hypOf (u4U τ) (isU4_U h hτ) =
        hypOf (u4U τ) (isU4_U h hτ) * hypOf (u4U τ) (isU4_U h hτ) *
          hypOf (u4T h l) (isU4_T h hl) := by
      rw [← hypOf_mul, ← hypOf_mul, ← hypOf_mul]
      exact hypOf_ext _ _ (u4T_mul_U h h3)
    rw [commutatorElement_def, hmul]
    group
  have hTL : ⁅hypOf (u4T h l) (isU4_T h hl), hypOf (u4L τ) (isU4_L h hτ)⁆ =
      hypOf (u4L τ) (isU4_L h hτ) := by
    have hmul : hypOf (u4T h l) (isU4_T h hl) * hypOf (u4L τ) (isU4_L h hτ) =
        hypOf (u4L τ) (isU4_L h hτ) * hypOf (u4L τ) (isU4_L h hτ) *
          hypOf (u4T h l) (isU4_T h hl) := by
      rw [← hypOf_mul, ← hypOf_mul, ← hypOf_mul]
      exact hypOf_ext _ _ (u4T_mul_L h h3)
    rw [commutatorElement_def, hmul]
    group
  have hcU := hc _ _ hTfix hUfix
  have hcL := hc _ _ hTfix hLfix
  rw [hTU] at hcU
  rw [hTL] at hcL
  have hconv : ∀ (X : Matrix (Fin 4) (Fin 4) K) (hX : IsU4 h X), x * hypOf X hX = hypOf X hX * x →
      fromHyp ((x : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) * X =
        X * fromHyp ((x : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) := by
    intro X hX hxX
    have h1 := congrArg (fun y : ↥(hypSU h 2 0) => fromHyp ((y : GL (HypIndex 2 0) K) :
      Matrix (HypIndex 2 0) (HypIndex 2 0) K)) hxX
    simp only [Subgroup.coe_mul, Units.val_mul, fromHyp_mul, coe_hypOf, fromHyp_toHyp] at h1
    exact h1
  exact mem_fixSub.1 (mem_fixSub_alpha0_of_comm_hyp h x
    (u4_cent4 hτ0 hτ0 (hconv _ _ hcU) (hconv _ _ hcL)))

end Cent3Std

end Cent

end U4C1

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
