module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.Enumeration.Bounds
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Enumeration.Search
import Mathlib.Tactic.FinCases
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.LyonsUnitaryFour

@[expose] def lyonsOrbit (r : LyonsRow) : List LyonsRow :=
  if r.rotate = r then [r]
  else if r.rotate.rotate = r then [r, r.rotate]
  else [r, r.rotate, r.rotate.rotate, r.rotate.rotate.rotate]

@[expose] def lyonsOrbitReps : List LyonsRow :=
  [(-3, 0, 0, 0, 0, 1), (-2, 1, 0, 0, 0, 1), (-2, 1, 1, 1, 1, 2), (-1, 0, 0, 0, 1, 2),
    (-1, 0, 0, 0, 2, 1), (-1, 0, 0, 1, 0, 2), (-1, 2, 0, 0, 0, 1), (-1, 2, 1, 1, 1, 2),
    (-1, 2, 2, 2, 2, 3), (0, 1, 0, 0, 1, 2), (0, 1, 0, 0, 2, 1), (0, 1, 0, 1, 0, 2),
    (0, 2, 0, 0, 1, 1), (0, 2, 2, 2, 3, 3), (0, 3, 2, 2, 2, 3), (1, -1, 0, 0, 1, 1),
    (1, 0, -1, 0, 1, 1), (1, 0, -1, 1, 0, 1), (1, 0, -1, 1, 1, 0), (1, 2, 2, 3, 3, 3),
    (1, 3, 2, 2, 3, 3), (1, 3, 2, 3, 2, 3), (3, 0, 0, 1, 1, 1), (3, 1, 0, 0, 1, 1),
    (3, 1, 0, 1, 0, 1), (-2, 0, 0, 0, 1, 1), (-1, 1, 1, 1, 2, 2), (-1, 1, -1, 1, 1, 1),
    (-1, 1, 0, 0, 0, 2), (0, 2, 1, 1, 2, 2), (2, 0, 0, 0, 1, 1), (0, 2, 2, 3, 2, 3),
    (1, 2, 1, 2, 2, 2), (2, 1, 0, 0, 0, 1), (-1, 1, 0, 0, 1, 1), (0, 1, 1, 2, 2, 2),
    (1, 2, 0, 1, 1, 1), (2, 1, 1, 1, 1, 2), (1, 1, -1, 0, 1, 0), (-2, 0, 0, 1, 0, 1),
    (-1, 1, 1, 2, 1, 2), (1, 1, -1, 0, 0, 1), (1, 1, -1, 1, 0, 0), (-1, 0, 0, 1, 1, 1),
    (0, 0, 0, 1, 2, 1), (1, 1, 0, 1, 2, 1), (0, 2, 1, 2, 1, 2), (0, 0, 0, 1, 1, 2),
    (0, 0, 0, 2, 1, 1), (1, 1, 0, 1, 1, 2), (1, 1, 0, 2, 1, 1), (1, 0, 1, 1, 1, 2),
    (0, 2, 0, 1, 0, 1), (2, 0, 0, 1, 0, 1), (-1, 1, 0, 1, 0, 1), (1, -1, 0, 1, 0, 1),
    (0, 1, 0, 1, 1, 1), (1, 0, 0, 0, 0, 1), (-1, 3, 3, 3, 3, 3), (-2, 2, 2, 2, 2, 2),
    (-3, 1, 1, 1, 1, 1), (-1, 3, 2, 2, 2, 2), (-3, 1, 0, 0, 0, 0), (-2, 2, 1, 1, 1, 1),
    (2, 2, 2, 2, 2, 2), (-1, -1, 1, 1, 1, 1), (2, 2, 1, 1, 1, 1), (1, 1, 2, 2, 2, 2),
    (1, 1, 0, 0, 0, 0), (0, 0, 1, 1, 1, 1), (1, 1, 1, 1, 1, 1)]

@[expose] def lyonsAdmissibleRows : List LyonsRow := lyonsOrbitReps.flatMap lyonsOrbit

@[expose] def LyonsRow.admissibleBool (r : LyonsRow) : Bool :=
  decide (0 < r.fourierSum) && decide ((r.1 - r.fourierSum) % 4 = 0) &&
    decide (r.strictContribution < 64)

theorem LyonsRow.admissibleBool_eq_true {r : LyonsRow} (hr : r.Admissible) :
    r.admissibleBool = true := by
  have h := hr.modEq
  simp only [Int.ModEq] at h
  have h' : (r.1 - r.fourierSum) % 4 = 0 := by omega
  simp [admissibleBool, hr.fourierSum_pos, h', hr.strictContribution_lt]

theorem LyonsRow.admissible_of_admissibleBool {r : LyonsRow} (hr : r.admissibleBool = true) :
    r.Admissible := by
  simp only [admissibleBool, Bool.and_eq_true, decide_eq_true_eq] at hr
  obtain ⟨⟨h1, h2⟩, h3⟩ := hr
  exact ⟨h1, by simp only [Int.ModEq]; omega, h3⟩

instance : DecidablePred LyonsRow.Admissible := fun r =>
  decidable_of_iff (r.admissibleBool = true)
    ⟨LyonsRow.admissible_of_admissibleBool, LyonsRow.admissibleBool_eq_true⟩

private theorem box_check :
    (lyonsCoordRange.all fun a => lyonsCoordRange.all fun b => lyonsCoordRange.all fun c =>
      lyonsCoordRange.all fun d => lyonsCoordRange.all fun e =>
        !(decide (0 < a + b + c + d + e) &&
          decide (16 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) - 3 * (a + b + c + d + e) ^ 2 <
            64)) ||
        lyonsCoordRange.all fun t =>
          !(LyonsRow.admissibleBool (t, a, b, c, d, e)) ||
            lyonsAdmissibleRows.contains (t, a, b, c, d, e)) = true := by
  decide +kernel

theorem mem_lyonsAdmissibleRows {r : LyonsRow} (hr : r.Admissible) : r ∈ lyonsAdmissibleRows := by
  have hb := fun i => mem_lyonsCoordRange (LyonsRow.abs_toVec_le_three hr.strictContribution_lt i)
  obtain ⟨t, a, b, c, d, e⟩ := r
  have ht := hb 0; have ha := hb 1; have hb' := hb 2; have hc := hb 3; have hd := hb 4
  have he := hb 5
  simp only [LyonsRow.toVec, Matrix.cons_val] at ht ha hb' hc hd he
  have h := box_check
  simp only [List.all_eq_true] at h
  have h' := h a ha b hb' c hc d hd e he
  have hpos : 0 < a + b + c + d + e := hr.fourierSum_pos
  have hq : 16 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) - 3 * (a + b + c + d + e) ^ 2 < 64 := by
    have := hr.strictContribution_lt
    simp only [LyonsRow.strictContribution] at this
    nlinarith [sq_nonneg t]
  simp only [hpos, hq, decide_true, Bool.and_self, Bool.not_true, Bool.false_or,
    List.all_eq_true] at h'
  have h'' := h' t ht
  simp only [LyonsRow.admissibleBool_eq_true hr, Bool.not_true, Bool.false_or,
    List.contains_iff_mem] at h''
  exact h''

theorem lyonsAdmissibleRows_nodup : lyonsAdmissibleRows.Nodup := by
  decide +kernel

theorem count_eq_of_mem_lyonsOrbit {M : Multiset LyonsRow} (hM : M.map LyonsRow.rotate = M)
    {r x : LyonsRow} (hx : x ∈ lyonsOrbit r) : M.count x = M.count r := by
  have h1 := count_rotate_of_map_rotate hM r
  have h2 := count_rotate_of_map_rotate hM r.rotate
  have h3 := count_rotate_of_map_rotate hM r.rotate.rotate
  unfold lyonsOrbit at hx
  split_ifs at hx <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hx <;>
    rcases hx with rfl | rfl | rfl | rfl <;> omega

theorem sum_map_eq_sum_lyonsOrbits {M : Multiset LyonsRow}
    (hsupp : ∀ x ∈ M, x ∈ lyonsAdmissibleRows) (hM : M.map LyonsRow.rotate = M)
    (φ : LyonsRow → ℕ) :
    (M.map φ).sum = (lyonsOrbitReps.map fun r => M.count r * ((lyonsOrbit r).map φ).sum).sum := by
  classical
  rw [Finset.sum_multiset_map_count]
  rw [Finset.sum_subset (s₂ := lyonsAdmissibleRows.toFinset)]
  · rw [List.sum_toFinset _ lyonsAdmissibleRows_nodup, lyonsAdmissibleRows, List.flatMap,
      List.map_flatten, List.sum_flatten, List.map_map, List.map_map]
    congr 1
    apply List.map_congr_left
    intro r _
    simp only [Function.comp_apply, smul_eq_mul]
    rw [← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro x hx
    rw [count_eq_of_mem_lyonsOrbit hM hx]
  · intro x hx
    rw [Multiset.mem_toFinset] at hx
    exact List.mem_toFinset.mpr (hsupp x hx)
  · intro x _ hx
    rw [Multiset.mem_toFinset, ← Multiset.count_eq_zero] at hx
    rw [hx, zero_smul]

theorem eq_of_map_count_lyonsOrbitReps {M M' : Multiset LyonsRow}
    (hsupp : ∀ x ∈ M, x ∈ lyonsAdmissibleRows) (hsupp' : ∀ x ∈ M', x ∈ lyonsAdmissibleRows)
    (hM : M.map LyonsRow.rotate = M) (hM' : M'.map LyonsRow.rotate = M')
    (h : lyonsOrbitReps.map M.count = lyonsOrbitReps.map M'.count) : M = M' := by
  ext x
  by_cases hx : x ∈ lyonsAdmissibleRows
  · obtain ⟨r, hr, hxr⟩ := List.mem_flatMap.mp hx
    rw [count_eq_of_mem_lyonsOrbit hM hxr, count_eq_of_mem_lyonsOrbit hM' hxr]
    exact List.map_inj_left.mp h r hr
  · rw [Multiset.count_eq_zero.mpr fun hxM => hx (hsupp x hxM),
      Multiset.count_eq_zero.mpr fun hxM => hx (hsupp' x hxM)]

@[expose] def lyonsRowMoments : LyonsRow → LyonsMoments
  | (t, a, b, c, d, _) =>
    ⟨t.natAbs * t.natAbs, a.natAbs * a.natAbs, b.natAbs * b.natAbs, (t - a).natAbs * (t - a).natAbs,
      (t - b).natAbs * (t - b).natAbs, (a - b).natAbs * (a - b).natAbs,
      (b - c).natAbs * (b - c).natAbs, (b - d).natAbs * (b - d).natAbs⟩

@[expose] def lyonsOrbitMoments (r : LyonsRow) : LyonsMoments :=
  lyonsMomentSum ((lyonsOrbit r).map lyonsRowMoments)

@[expose] def lyonsMultisetMoments (M : Multiset LyonsRow) : LyonsMoments :=
  ⟨(M.map fun r => (lyonsRowMoments r).m0).sum, (M.map fun r => (lyonsRowMoments r).m1).sum,
    (M.map fun r => (lyonsRowMoments r).m2).sum, (M.map fun r => (lyonsRowMoments r).m3).sum,
    (M.map fun r => (lyonsRowMoments r).m4).sum, (M.map fun r => (lyonsRowMoments r).m5).sum,
    (M.map fun r => (lyonsRowMoments r).m6).sum, (M.map fun r => (lyonsRowMoments r).m7).sum⟩

theorem lyonsMultisetMoments_get (M : Multiset LyonsRow) (j : Fin 8) :
    (lyonsMultisetMoments M).get j = (M.map fun r => (lyonsRowMoments r).get j).sum := by
  fin_cases j <;> rfl

theorem lyonsMomentSum_get (ws : List LyonsMoments) (j : Fin 8) :
    (lyonsMomentSum ws).get j = (ws.map fun w => w.get j).sum := by
  induction ws with
  | nil => simp [lyonsMomentSum]
  | cons w ws ih =>
    simp only [lyonsMomentSum, List.foldr_cons, LyonsMoments.get_add, List.map_cons,
      List.sum_cons] at ih ⊢
    rw [ih]

theorem lyonsMultisetMoments_eq_combination {M : Multiset LyonsRow}
    (hsupp : ∀ x ∈ M, x ∈ lyonsAdmissibleRows) (hM : M.map LyonsRow.rotate = M) :
    lyonsMultisetMoments M =
      lyonsCombination (lyonsOrbitReps.map M.count) (lyonsOrbitReps.map lyonsOrbitMoments) := by
  apply LyonsMoments.ext_get
  intro j
  rw [lyonsMultisetMoments_get, lyonsCombination_map_get, sum_map_eq_sum_lyonsOrbits hsupp hM]
  congr 1
  apply List.map_congr_left
  intro r _
  rw [lyonsOrbitMoments, lyonsMomentSum_get, List.map_map]
  rfl

@[expose] def lyonsTargetMoments : LyonsMoments := ⟨16, 16, 16, 32, 32, 8, 8, 8⟩

theorem lyonsMultisetMoments_eq_target {M : Multiset LyonsRow} (hM : LyonsColumnConditions M) :
    lyonsMultisetMoments M = lyonsTargetMoments := by
  have hG := hM.gramSum_eq
  have key : ∀ (k l : Fin 6) (f : LyonsRow → ℕ),
      (∀ r : LyonsRow, (f r : ℤ) = (r.toVec k - r.toVec l) ^ 2) →
      ((M.map f).sum : ℤ) = gramSum M k k + gramSum M l l - 2 * gramSum M k l := by
    intro k l f hf
    rw [Nat.cast_multiset_sum, Multiset.map_map, ← sum_map_toVec_sub_sq]
    congr 1
    exact Multiset.map_congr rfl fun r _ => hf r
  have key2 : ∀ (k : Fin 6) (f : LyonsRow → ℕ),
      (∀ r : LyonsRow, (f r : ℤ) = r.toVec k ^ 2) → ((M.map f).sum : ℤ) = gramSum M k k := by
    intro k f hf
    rw [Nat.cast_multiset_sum, Multiset.map_map, ← sum_map_toVec_sq]
    congr 1
    exact Multiset.map_congr rfl fun r _ => hf r
  have nsq : ∀ x : ℤ, ((x.natAbs * x.natAbs : ℕ) : ℤ) = x ^ 2 := fun x => by
    rw [Nat.cast_mul, Int.natAbs_mul_self', sq]
  apply LyonsMoments.ext_get
  intro j
  rw [lyonsMultisetMoments_get]
  apply Int.ofNat_inj.mp
  fin_cases j
  · rw [key2 0 _ fun ⟨t, a, b, c, d, e⟩ => nsq t, hG]; rfl
  · rw [key2 1 _ fun ⟨t, a, b, c, d, e⟩ => nsq a, hG]; rfl
  · rw [key2 2 _ fun ⟨t, a, b, c, d, e⟩ => nsq b, hG]; rfl
  · rw [key 0 1 _ fun ⟨t, a, b, c, d, e⟩ => nsq (t - a), hG]; rfl
  · rw [key 0 2 _ fun ⟨t, a, b, c, d, e⟩ => nsq (t - b), hG]; rfl
  · rw [key 1 2 _ fun ⟨t, a, b, c, d, e⟩ => nsq (a - b), hG]; rfl
  · rw [key 2 3 _ fun ⟨t, a, b, c, d, e⟩ => nsq (b - c), hG]; rfl
  · rw [key 2 4 _ fun ⟨t, a, b, c, d, e⟩ => nsq (b - d), hG]; rfl

end CFSG.LyonsUnitaryFour
