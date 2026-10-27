module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTModel

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs

section Model

variable {F : Type} [Field F] [CharP F 2]

theorem q2Par_five (a : Fin (2 * 2 + 1)) : q2Par 2 1 a = ![1, 0, 3, 2, 4] a := by
  have h0 : (0 : Fin (2 * 2 + 1)) = q2Coord 2 1 (Sum.inl (Sum.inl 0)) :=
    Fin.ext (by rw [q2Coord_inl_inl]; rfl)
  have h1 : (1 : Fin (2 * 2 + 1)) = q2Coord 2 1 (Sum.inl (Sum.inr 0)) :=
    Fin.ext (by rw [q2Coord_inl_inr]; rfl)
  have h2 : (2 : Fin (2 * 2 + 1)) = q2Coord 2 1 (Sum.inl (Sum.inl 1)) :=
    Fin.ext (by rw [q2Coord_inl_inl]; rfl)
  have h3 : (3 : Fin (2 * 2 + 1)) = q2Coord 2 1 (Sum.inl (Sum.inr 1)) :=
    Fin.ext (by rw [q2Coord_inl_inr]; rfl)
  have h4 : (4 : Fin (2 * 2 + 1)) = q2Coord 2 1 (Sum.inr 0) :=
    Fin.ext (by rw [q2Coord_inr]; rfl)
  fin_cases a
  · change q2Par 2 1 0 = 1
    rw [h0, q2Par_q2Coord, h1]
    rfl
  · change q2Par 2 1 1 = 0
    rw [h1, q2Par_q2Coord, h0]
    rfl
  · change q2Par 2 1 2 = 3
    rw [h2, q2Par_q2Coord, h3]
    rfl
  · change q2Par 2 1 3 = 2
    rw [h3, q2Par_q2Coord, h2]
    rfl
  · change q2Par 2 1 4 = 4
    rw [h4, q2Par_q2Coord]
    rfl

theorem transvection_mul_self_charTwo {n : ℕ} {a b : Fin n} (hab : a ≠ b) (c : F) :
    SpecialLinearGroup.transvection hab c * SpecialLinearGroup.transvection hab c = 1 := by
  rw [← Matrix.SpecialLinearGroup.transvection_add, CharTwo.add_self_eq_zero,
    Matrix.SpecialLinearGroup.transvection_coeff_zero]

theorem transvection_inv_charTwo {n : ℕ} {a b : Fin n} (hab : a ≠ b) (c : F) :
    (SpecialLinearGroup.transvection hab c)⁻¹ = SpecialLinearGroup.transvection hab c :=
  inv_eq_of_mul_eq_one_right (transvection_mul_self_charTwo hab c)

theorem ctGraph_transvection {N : ℕ} {a b : Fin (2 * N + 1)} (hab : a ≠ b)
    (hab' : q2Par N 1 b ≠ q2Par N 1 a) (c : F) :
    ctGraph 1 (SpecialLinearGroup.transvection hab c) =
      SpecialLinearGroup.transvection hab' c := by
  apply Subtype.ext
  ext i j
  rw [coe_ctGraph, q2GramMat_mul_mul_apply, transpose_apply, transvection_inv_charTwo,
    SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_coe]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  have hinj : ∀ x y : Fin (2 * N + 1), q2Par N 1 x = q2Par N 1 y ↔ x = y := fun x y =>
    ⟨fun h => by rw [← q2Par_q2Par x, h, q2Par_q2Par], fun h => by rw [h]⟩
  have e1 : (q2Par N 1 j = q2Par N 1 i) ↔ (i = j) := (hinj j i).trans eq_comm
  have e2 : (a = q2Par N 1 j ∧ b = q2Par N 1 i) ↔ (q2Par N 1 b = i ∧ q2Par N 1 a = j) := by
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [h2, q2Par_q2Par], by rw [h1, q2Par_q2Par]⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [← h2, q2Par_q2Par], by rw [← h1, q2Par_q2Par]⟩
  simp only [e1, e2]

theorem ctGraph_transvection' {N : ℕ} {a b a' b' : Fin (2 * N + 1)} (hab : a ≠ b)
    (ha' : q2Par N 1 b = a') (hb' : q2Par N 1 a = b') (hab' : a' ≠ b') (c : F) :
    ctGraph 1 (SpecialLinearGroup.transvection hab c) =
      SpecialLinearGroup.transvection hab' c := by
  subst ha' hb'
  exact ctGraph_transvection hab hab' c

omit [CharP F 2] in
theorem transvection_not_mem_center_of_ne_zero {n : ℕ} {a b : Fin n} (hab : a ≠ b) {c : F}
    (hc : c ≠ 0) :
    SpecialLinearGroup.transvection hab c ∉ Subgroup.center (SpecialLinearGroup (Fin n) F) := by
  intro h
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 h
  have h1 := congrFun (congrFun hr a) b
  rw [SpecialLinearGroup.transvection_coe] at h1
  simp [hab] at h1
  exact hc h1.symm

variable (F) in
@[expose] noncomputable def oddRegUnip : SpecialLinearGroup (Fin (2 * 2 + 1)) F :=
  SpecialLinearGroup.transvection (show (2 : Fin (2 * 2 + 1)) ≠ 4 by decide) 1 *
    SpecialLinearGroup.transvection (show (4 : Fin (2 * 2 + 1)) ≠ 3 by decide) 1 *
      SpecialLinearGroup.transvection (show (2 : Fin (2 * 2 + 1)) ≠ 3 by decide) 1

variable (F) in
@[expose] noncomputable def oddZ : SpecialLinearGroup (Fin (2 * 2 + 1)) F :=
  SpecialLinearGroup.transvection (show (2 : Fin (2 * 2 + 1)) ≠ 3 by decide) 1

omit [CharP F 2] in
theorem transvection_four_three_two_four :
    SpecialLinearGroup.transvection (show (4 : Fin (2 * 2 + 1)) ≠ 3 by decide) (1 : F) *
      SpecialLinearGroup.transvection (show (2 : Fin (2 * 2 + 1)) ≠ 4 by decide) 1 *
        SpecialLinearGroup.transvection (show (2 : Fin (2 * 2 + 1)) ≠ 3 by decide) 1 =
      SpecialLinearGroup.transvection (show (2 : Fin (2 * 2 + 1)) ≠ 4 by decide) 1 *
        SpecialLinearGroup.transvection (show (4 : Fin (2 * 2 + 1)) ≠ 3 by decide) 1 := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_five, Matrix.single_apply, Matrix.one_apply]

theorem ctGraph_oddRegUnip : ctGraph 1 (oddRegUnip F) = oddRegUnip F * oddZ F := by
  have h4 : q2Par 2 1 (4 : Fin (2 * 2 + 1)) = 4 := q2Par_five 4
  have h2 : q2Par 2 1 (2 : Fin (2 * 2 + 1)) = 3 := q2Par_five 2
  have h3 : q2Par 2 1 (3 : Fin (2 * 2 + 1)) = 2 := q2Par_five 3
  rw [oddRegUnip, map_mul, map_mul, ctGraph_transvection' _ h4 h2 (by decide),
    ctGraph_transvection' _ h3 h4 (by decide), ctGraph_transvection' _ h3 h2 (by decide),
    transvection_four_three_two_four, oddZ, mul_assoc _ (SpecialLinearGroup.transvection _ _),
    transvection_mul_self_charTwo, mul_one]

end Model

end CFSG.SeitzReduction.SymplecticPilot
