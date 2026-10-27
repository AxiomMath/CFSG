module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.Enumeration.Rows
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.LyonsUnitaryFour

open Matrix

namespace LyonsRow

theorem four_mul_sq_le_strictContribution (r : LyonsRow) (i : Fin 6) :
    4 * r.toVec i ^ 2 ≤ r.strictContribution := by
  obtain ⟨t, a, b, c, d, e⟩ := r
  simp only [strictContribution]
  fin_cases i <;> simp only [toVec] <;> simp
  · nlinarith [sq_nonneg (a + b + c + d + e), sq_nonneg (a - b), sq_nonneg (a - c),
      sq_nonneg (a - d), sq_nonneg (a - e), sq_nonneg (b - c), sq_nonneg (b - d),
      sq_nonneg (b - e), sq_nonneg (c - d), sq_nonneg (c - e), sq_nonneg (d - e)]
  · nlinarith [sq_nonneg t, sq_nonneg (3 * a - (b + c + d + e)), sq_nonneg (b - c),
      sq_nonneg (b - d), sq_nonneg (b - e), sq_nonneg (c - d), sq_nonneg (c - e),
      sq_nonneg (d - e)]
  · nlinarith [sq_nonneg t, sq_nonneg (3 * b - (a + c + d + e)), sq_nonneg (a - c),
      sq_nonneg (a - d), sq_nonneg (a - e), sq_nonneg (c - d), sq_nonneg (c - e),
      sq_nonneg (d - e)]
  · nlinarith [sq_nonneg t, sq_nonneg (3 * c - (a + b + d + e)), sq_nonneg (a - b),
      sq_nonneg (a - d), sq_nonneg (a - e), sq_nonneg (b - d), sq_nonneg (b - e),
      sq_nonneg (d - e)]
  · nlinarith [sq_nonneg t, sq_nonneg (3 * d - (a + b + c + e)), sq_nonneg (a - b),
      sq_nonneg (a - c), sq_nonneg (a - e), sq_nonneg (b - c), sq_nonneg (b - e),
      sq_nonneg (c - e)]
  · nlinarith [sq_nonneg t, sq_nonneg (3 * e - (a + b + c + d)), sq_nonneg (a - b),
      sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d),
      sq_nonneg (c - d)]

theorem abs_toVec_le_three {r : LyonsRow} (hr : r.strictContribution < 64) (i : Fin 6) :
    |r.toVec i| ≤ 3 := by
  have h := r.four_mul_sq_le_strictContribution i
  rw [abs_le]
  constructor <;> nlinarith

theorem rotate_eq_self_iff (r : LyonsRow) :
    r.rotate = r ↔ ∃ t a b : ℤ, r = (t, a, b, b, b, b) := by
  obtain ⟨t, a, b, c, d, e⟩ := r
  constructor
  · intro h
    simp only [rotate, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl, rfl, rfl, -⟩ := h
    exact ⟨t, a, _, rfl⟩
  · rintro ⟨t', a', b', h⟩
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
    rfl

end LyonsRow

@[expose] def lyonsFixedTriples : List (ℤ × ℤ × ℤ) :=
  [(-3, 1, 0), (-3, 1, 1), (-2, 2, 1), (-2, 2, 2), (-1, -1, 1), (-1, 3, 2), (-1, 3, 3), (0, 0, 1),
    (1, 1, 0), (1, 1, 1), (1, 1, 2), (2, 2, 1), (2, 2, 2)]

theorem lyonsFixedTriples_sub : ∀ x ∈ lyonsFixedTriples, x.1 = x.2.1 ∨ x.1 = x.2.1 - 4 := by
  decide

@[expose] def lyonsCoordRange : List ℤ := [-3, -2, -1, 0, 1, 2, 3]

theorem mem_lyonsCoordRange {x : ℤ} (h : |x| ≤ 3) : x ∈ lyonsCoordRange := by
  rw [abs_le] at h
  obtain ⟨h1, h2⟩ := h
  have : x = -3 ∨ x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem fixed_check :
    (lyonsCoordRange.all fun t => lyonsCoordRange.all fun a => lyonsCoordRange.all fun b =>
      !(decide (0 < a + 4 * b) && decide ((t - (a + 4 * b)) % 4 = 0) &&
        decide (LyonsRow.strictContribution (t, a, b, b, b, b) < 64)) ||
      decide ((t, a, b) ∈ lyonsFixedTriples)) = true := by
  decide +kernel

theorem LyonsRow.exists_mem_lyonsFixedTriples {r : LyonsRow} (hr : r.Admissible)
    (hfix : r.rotate = r) :
    ∃ t a b : ℤ, r = (t, a, b, b, b, b) ∧ (t, a, b) ∈ lyonsFixedTriples := by
  obtain ⟨t, a, b, rfl⟩ := (LyonsRow.rotate_eq_self_iff r).mp hfix
  refine ⟨t, a, b, rfl, ?_⟩
  have ht := mem_lyonsCoordRange (LyonsRow.abs_toVec_le_three hr.strictContribution_lt 0)
  have ha := mem_lyonsCoordRange (LyonsRow.abs_toVec_le_three hr.strictContribution_lt 1)
  have hb := mem_lyonsCoordRange (LyonsRow.abs_toVec_le_three hr.strictContribution_lt 2)
  simp only [LyonsRow.toVec, Matrix.cons_val] at ht ha hb
  have h := fixed_check
  simp only [List.all_eq_true] at h
  have h' := h t ht a ha b hb
  have hpos : 0 < a + 4 * b := by
    have := hr.fourierSum_pos
    simp only [LyonsRow.fourierSum] at this
    linarith
  have hmod : (t - (a + 4 * b)) % 4 = 0 := by
    have := hr.modEq
    simp only [LyonsRow.fourierSum, Int.ModEq] at this
    omega
  have hq := hr.strictContribution_lt
  simp only [hpos, hmod, hq, decide_true, Bool.and_self, Bool.not_true, Bool.false_or,
    decide_eq_true_eq] at h'
  exact h'

theorem LyonsRow.fixed_toVec_zero {r : LyonsRow} (hr : r.Admissible) (hfix : r.rotate = r) :
    r.toVec 0 = r.toVec 1 ∨ r.toVec 0 = r.toVec 1 - 4 := by
  obtain ⟨t, a, b, rfl, hmem⟩ := LyonsRow.exists_mem_lyonsFixedTriples hr hfix
  simp only [LyonsRow.toVec, Matrix.cons_val]
  exact lyonsFixedTriples_sub _ hmem

@[expose] def lyonsEightMoments (M : Multiset LyonsRow) : Fin 8 → ℤ :=
  ![(M.map fun r => r.toVec 0 ^ 2).sum, (M.map fun r => r.toVec 0 * r.toVec 1).sum,
    (M.map fun r => r.toVec 0 * r.toVec 2).sum, (M.map fun r => r.toVec 1 ^ 2).sum,
    (M.map fun r => r.toVec 1 * r.toVec 2).sum, (M.map fun r => r.toVec 2 ^ 2).sum,
    (M.map fun r => (r.toVec 2 - r.toVec 3) ^ 2).sum,
    (M.map fun r => (r.toVec 2 - r.toVec 4) ^ 2).sum]

theorem sum_map_quadratic (M : Multiset LyonsRow) (Q : Matrix (Fin 6) (Fin 6) ℤ) :
    (M.map fun r => ∑ i, ∑ j, Q i j * (r.toVec i * r.toVec j)).sum =
      ∑ i, ∑ j, Q i j * gramSum M i j := by
  induction M using Multiset.induction_on with
  | empty => simp [gramSum]
  | cons r M ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, ih, gramSum, Matrix.add_apply,
      Matrix.vecMulVec_apply, mul_add, Finset.sum_add_distrib]

theorem gramSum_comm (M : Multiset LyonsRow) (i j : Fin 6) : gramSum M i j = gramSum M j i := by
  simp only [gramSum_apply, mul_comm]

theorem gramSum_perm_of_map_rotate {M : Multiset LyonsRow} (hM : M.map LyonsRow.rotate = M)
    (i j : Fin 6) :
    gramSum M (![0, 1, 5, 2, 3, 4] i) (![0, 1, 5, 2, 3, 4] j) = gramSum M i j := by
  conv_rhs => rw [← hM]
  simp only [gramSum_apply, Multiset.map_map, Function.comp_def, LyonsRow.toVec_rotate]

theorem sum_map_toVec_sq (M : Multiset LyonsRow) (k : Fin 6) :
    (M.map fun r => r.toVec k ^ 2).sum = gramSum M k k := by
  simp only [gramSum_apply, sq]

theorem sum_map_toVec_sub_sq (M : Multiset LyonsRow) (k l : Fin 6) :
    (M.map fun r => (r.toVec k - r.toVec l) ^ 2).sum =
      gramSum M k k + gramSum M l l - 2 * gramSum M k l := by
  simp only [gramSum_apply, ← Multiset.sum_map_mul_left, ← Multiset.sum_map_add,
    ← Multiset.sum_map_sub]
  congr 1
  apply Multiset.map_congr rfl
  intro r _
  ring

theorem lyonsEightMoments_eq (M : Multiset LyonsRow) :
    lyonsEightMoments M = ![gramSum M 0 0, gramSum M 0 1, gramSum M 0 2, gramSum M 1 1,
      gramSum M 1 2, gramSum M 2 2, gramSum M 2 2 + gramSum M 3 3 - 2 * gramSum M 2 3,
      gramSum M 2 2 + gramSum M 4 4 - 2 * gramSum M 2 4] := by
  have h6 := sum_map_toVec_sub_sq M
  ext k
  fin_cases k <;>
    simp only [lyonsEightMoments, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val] <;>
    first | exact h6 _ _ | simp only [gramSum_apply, sq]

@[expose] def lyonsDoubledGramOfMoments (m : Fin 8 → ℤ) : Matrix (Fin 6) (Fin 6) ℤ :=
  Matrix.of ![![2 * m 0, 2 * m 1, 2 * m 2, 2 * m 2, 2 * m 2, 2 * m 2],
    ![2 * m 1, 2 * m 3, 2 * m 4, 2 * m 4, 2 * m 4, 2 * m 4],
    ![2 * m 2, 2 * m 4, 2 * m 5, 2 * m 5 - m 6, 2 * m 5 - m 7, 2 * m 5 - m 6],
    ![2 * m 2, 2 * m 4, 2 * m 5 - m 6, 2 * m 5, 2 * m 5 - m 6, 2 * m 5 - m 7],
    ![2 * m 2, 2 * m 4, 2 * m 5 - m 7, 2 * m 5 - m 6, 2 * m 5, 2 * m 5 - m 6],
    ![2 * m 2, 2 * m 4, 2 * m 5 - m 6, 2 * m 5 - m 7, 2 * m 5 - m 6, 2 * m 5]]

theorem two_mul_gramSum_of_map_rotate {M : Multiset LyonsRow} (hM : M.map LyonsRow.rotate = M)
    (i j : Fin 6) :
    2 * gramSum M i j = lyonsDoubledGramOfMoments (lyonsEightMoments M) i j := by
  have p := gramSum_perm_of_map_rotate hM
  have s := gramSum_comm M
  have p01 := p 0 1; have p02 := p 0 2; have p03 := p 0 3; have p04 := p 0 4
  have p12 := p 1 2; have p13 := p 1 3; have p14 := p 1 4
  have p22 := p 2 2; have p33 := p 3 3; have p44 := p 4 4
  have p23 := p 2 3; have p34 := p 3 4; have p45 := p 4 5; have p24 := p 2 4
  simp only [Matrix.cons_val] at p01 p02 p03 p04 p12 p13 p14 p22 p33 p44 p23 p34 p45 p24
  have s01 := s 0 1; have s02 := s 0 2; have s03 := s 0 3; have s04 := s 0 4; have s05 := s 0 5
  have s12 := s 1 2; have s13 := s 1 3; have s14 := s 1 4; have s15 := s 1 5
  have s23 := s 2 3; have s24 := s 2 4; have s25 := s 2 5; have s34 := s 3 4; have s35 := s 3 5
  have s45 := s 4 5
  rw [lyonsEightMoments_eq]
  fin_cases i <;> fin_cases j <;>
    simp only [lyonsDoubledGramOfMoments, Matrix.of_apply, Fin.isValue, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Matrix.cons_val] <;>
    omega

theorem gramSum_eq_of_lyonsEightMoments_eq {M M' : Multiset LyonsRow}
    (hM : M.map LyonsRow.rotate = M) (hM' : M'.map LyonsRow.rotate = M')
    (h : lyonsEightMoments M = lyonsEightMoments M') : gramSum M = gramSum M' := by
  ext i j
  have h1 := two_mul_gramSum_of_map_rotate hM i j
  have h2 := two_mul_gramSum_of_map_rotate hM' i j
  rw [h] at h1
  omega

theorem count_rotate_eq {M : Multiset LyonsRow} (hM : LyonsColumnConditions M) (r : LyonsRow) :
    M.count r.rotate = M.count r :=
  count_rotate_of_map_rotate hM.map_rotate r

theorem lyons_normalized_column_finite_bounds {M : Multiset LyonsRow}
    (hM : LyonsColumnConditions M) :
    (∀ r ∈ M, ∀ i, |r.toVec i| ≤ 3) ∧
    (M.map LyonsRow.strictContribution).sum = 384 ∧
    (M.map fun r => (r.toVec 0 - r.toVec 1) ^ 2).sum = 32 ∧
    lyonsEightMoments M = ![16, 0, 0, 16, 12, 16, 8, 8] ∧
    (∀ r ∈ M, r.rotate = r → r.toVec 0 = r.toVec 1 ∨ r.toVec 0 = r.toVec 1 - 4) ∧
    (M.filter fun r => r.rotate = r ∧ r.toVec 0 ≠ r.toVec 1).card ≤ 2 ∧
    (∀ r, M.count r.rotate = M.count r) := by
  have hG := hM.gramSum_eq
  have hq : ∀ r : LyonsRow, r.strictContribution =
      ∑ i, ∑ j, (Matrix.of ![![4, 0, 0, 0, 0, 0], ![0, 13, -3, -3, -3, -3],
        ![0, -3, 13, -3, -3, -3], ![0, -3, -3, 13, -3, -3], ![0, -3, -3, -3, 13, -3],
        ![0, -3, -3, -3, -3, 13]] : Matrix (Fin 6) (Fin 6) ℤ) i j * (r.toVec i * r.toVec j) := by
    rintro ⟨t, a, b, c, d, e⟩
    simp only [LyonsRow.strictContribution, LyonsRow.toVec, Fin.sum_univ_six, Matrix.of_apply,
      Matrix.cons_val]
    ring
  have hta : ∀ r : LyonsRow, (r.toVec 0 - r.toVec 1) ^ 2 =
      ∑ i, ∑ j, (Matrix.of ![![1, -1, 0, 0, 0, 0], ![-1, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
        ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]] :
          Matrix (Fin 6) (Fin 6) ℤ) i j * (r.toVec i * r.toVec j) := by
    rintro ⟨t, a, b, c, d, e⟩
    simp only [LyonsRow.toVec, Fin.sum_univ_six, Matrix.of_apply, Matrix.cons_val]
    ring
  have hsumq : (M.map LyonsRow.strictContribution).sum = 384 := by
    rw [show (LyonsRow.strictContribution) = _ from funext hq, sum_map_quadratic, hG]
    decide
  have hsumta : (M.map fun r => (r.toVec 0 - r.toVec 1) ^ 2).sum = 32 := by
    rw [show (fun r : LyonsRow => (r.toVec 0 - r.toVec 1) ^ 2) = _ from funext hta,
      sum_map_quadratic, hG]
    decide
  have hfix : ∀ r ∈ M, r.rotate = r → r.toVec 0 = r.toVec 1 ∨ r.toVec 0 = r.toVec 1 - 4 :=
    fun r hr hrot => LyonsRow.fixed_toVec_zero (hM.admissible r hr) hrot
  refine ⟨fun r hr i => LyonsRow.abs_toVec_le_three (hM.admissible r hr).strictContribution_lt i,
    hsumq, hsumta, ?_, hfix, ?_, count_rotate_eq hM⟩
  · rw [lyonsEightMoments_eq, hG]
    decide
  ·
    let P : LyonsRow → Prop := fun r => r.rotate = r ∧ r.toVec 0 ≠ r.toVec 1
    have hsplit := Multiset.filter_add_not P M
    have hsum := hsumta
    rw [← hsplit, Multiset.map_add, Multiset.sum_add] at hsum
    have h16 : ((M.filter P).map fun r => (r.toVec 0 - r.toVec 1) ^ 2).sum =
        16 * ((M.filter P).card : ℤ) := by
      rw [Multiset.map_congr rfl (g := fun _ => (16 : ℤ)), Multiset.map_const',
        Multiset.sum_replicate, nsmul_eq_mul, mul_comm]
      intro r hr
      obtain ⟨hrM, hrot, hne⟩ := Multiset.mem_filter.mp hr
      rcases hfix r hrM hrot with h | h
      · exact absurd h hne
      · rw [h]; ring
    have hnn : 0 ≤ ((M.filter fun r => ¬ P r).map fun r => (r.toVec 0 - r.toVec 1) ^ 2).sum :=
      Multiset.sum_nonneg fun x hx => by
        obtain ⟨r, -, rfl⟩ := Multiset.mem_map.mp hx
        positivity
    have : (16 : ℤ) * ((M.filter P).card : ℤ) ≤ 32 := by linarith
    change (M.filter P).card ≤ 2
    omega

end CFSG.LyonsUnitaryFour
