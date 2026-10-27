module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.FiveColumns.GramStrict
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Enumeration.Exhaustive
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LyonsUnitaryFour

open Finset

namespace LyonsRow

theorem fourierSum_neg (r : LyonsRow) : (-r).fourierSum = -r.fourierSum := by
  obtain ⟨t, a, b, c, d, e⟩ := r
  change fourierSum (-t, -a, -b, -c, -d, -e) = _
  simp only [fourierSum]
  ring

theorem strictContribution_neg (r : LyonsRow) :
    (-r).strictContribution = r.strictContribution := by
  obtain ⟨t, a, b, c, d, e⟩ := r
  change strictContribution (-t, -a, -b, -c, -d, -e) = _
  simp only [strictContribution]
  ring

theorem rotate_neg (r : LyonsRow) : (-r).rotate = -r.rotate := by
  obtain ⟨t, a, b, c, d, e⟩ := r
  rfl

theorem fourierSum_rotate (r : LyonsRow) : r.rotate.fourierSum = r.fourierSum := by
  obtain ⟨t, a, b, c, d, e⟩ := r
  simp only [rotate, fourierSum]
  ring

theorem toVec_neg (r : LyonsRow) (i : Fin 6) : (-r).toVec i = -r.toVec i := by
  obtain ⟨t, a, b, c, d, e⟩ := r
  fin_cases i <;> rfl

end LyonsRow

@[expose] def columnRow {ι : Type*} (dt : ι → ℤ) (d : Fin 5 → ι → ℤ) (χ : ι) : LyonsRow :=
  (dt χ, d 0 χ, d 1 χ, d 2 χ, d 4 χ, d 3 χ)

@[expose] def normalizedColumnRow {ι : Type*} (dt : ι → ℤ) (d : Fin 5 → ι → ℤ) (χ : ι) :
    LyonsRow :=
  if 0 < (columnRow dt d χ).fourierSum then columnRow dt d χ else -columnRow dt d χ

theorem columnRow_fourierSum {ι : Type*} (dt : ι → ℤ) (d : Fin 5 → ι → ℤ) (χ : ι) :
    (columnRow dt d χ).fourierSum = ∑ i, d i χ := by
  simp only [columnRow, LyonsRow.fourierSum, Fin.sum_univ_five]
  ring

theorem columnRow_strictContribution {ι : Type*} (dt : ι → ℤ) (d : Fin 5 → ι → ℤ) (χ : ι) :
    (columnRow dt d χ).strictContribution =
      4 * dt χ ^ 2 + 16 * ∑ i, d i χ ^ 2 - 3 * (∑ i, d i χ) ^ 2 := by
  simp only [columnRow, LyonsRow.strictContribution, Fin.sum_univ_five]
  ring

theorem columnRow_toVec {ι : Type*} (dt : ι → ℤ) (d : Fin 5 → ι → ℤ) (χ : ι) :
    (columnRow dt d χ).toVec = ![dt χ, d 0 χ, d 1 χ, d 2 χ, d 4 χ, d 3 χ] := rfl

theorem normalizedColumnRow_toVec_mul {ι : Type*} (dt : ι → ℤ) (d : Fin 5 → ι → ℤ) (χ : ι)
    (a c : Fin 6) :
    (normalizedColumnRow dt d χ).toVec a * (normalizedColumnRow dt d χ).toVec c =
      (columnRow dt d χ).toVec a * (columnRow dt d χ).toVec c := by
  unfold normalizedColumnRow
  split_ifs
  · rfl
  · rw [LyonsRow.toVec_neg, LyonsRow.toVec_neg, neg_mul_neg]

theorem lyons_column_data_mem_configurations {ι : Type*} [DecidableEq ι] (B : Finset ι)
    (w dt : ι → ℤ) (d : Fin 5 → ι → ℤ) (hw : ∀ χ ∈ B, w χ ≠ 0)
    (htt : ∑ χ ∈ B, dt χ * dt χ = 16) (htd : ∀ i, ∑ χ ∈ B, dt χ * d i χ = 0)
    (hdd : ∀ i l, ∑ χ ∈ B, d i χ * d l χ = if i = l then 16 else 12)
    (hwt : ∑ χ ∈ B, dt χ * w χ = 0) (hwd : ∀ i, ∑ χ ∈ B, d i χ * w χ = 0)
    (hcong : ∀ χ ∈ B, dt χ ≡ ∑ i, d i χ [ZMOD 4]) (hnz : ∀ χ ∈ B, ∑ i, d i χ ≠ 0)
    (τ : Equiv.Perm ι) (hτB : ∀ χ, τ χ ∈ B ↔ χ ∈ B) (hτt : ∀ χ ∈ B, dt (τ χ) = dt χ)
    (hτd : ∀ χ ∈ B, ∀ i, d i (τ χ) = d (3 * i) χ) {p : ι} (hp : p ∈ B) (hpt : dt p = 1)
    (hpd : ∀ i, d i p = if i = 0 then 1 else 0) :
    B.val.map (normalizedColumnRow dt d) ∈ lyonsConfigurations := by
  set M := B.val.map (normalizedColumnRow dt d) with hM
  refine lyons_integral_column_exhaustive_enumeration.1 M ⟨?_, ?_, ?_⟩ ?_
  ·
    intro r hr
    obtain ⟨χ, hχ, rfl⟩ := Multiset.mem_map.mp hr
    have hχB : χ ∈ B := hχ
    have hstrict : (columnRow dt d χ).strictContribution < 64 := by
      rw [columnRow_strictContribution]
      have hreal := six_column_strict_contribution_lt B (fun k => (dt k : ℝ))
        (fun k => (w k : ℝ)) (fun i k => (d i k : ℝ)) (by exact_mod_cast htt)
        (fun i => by exact_mod_cast htd i)
        (fun i l => by
          have h := hdd i l
          split_ifs at h ⊢ <;> exact_mod_cast h)
        (by exact_mod_cast hwt) (fun i => by exact_mod_cast hwd i) hχB
        (by exact_mod_cast hw χ hχB)
      exact_mod_cast hreal
    have hcong' := hcong χ hχB
    rw [← columnRow_fourierSum] at hcong'
    have hnz' := hnz χ hχB
    rw [← columnRow_fourierSum] at hnz'
    unfold normalizedColumnRow
    split_ifs with hpos
    · exact ⟨hpos, hcong', hstrict⟩
    · refine ⟨?_, ?_, ?_⟩
      · rw [LyonsRow.fourierSum_neg]
        have : (columnRow dt d χ).fourierSum < 0 := lt_of_le_of_ne (not_lt.mp hpos) hnz'
        linarith
      · rw [LyonsRow.fourierSum_neg]
        exact hcong'.neg
      · rw [LyonsRow.strictContribution_neg]
        exact hstrict
  ·
    ext a c
    rw [gramSum_apply, hM, Multiset.map_map]
    change (B.val.map fun χ => (normalizedColumnRow dt d χ).toVec a *
      (normalizedColumnRow dt d χ).toVec c).sum = _
    simp only [normalizedColumnRow_toVec_mul]
    change ∑ χ ∈ B, (columnRow dt d χ).toVec a * (columnRow dt d χ).toVec c = _
    have htd' : ∀ i, ∑ χ ∈ B, d i χ * dt χ = 0 := fun i => by
      rw [← htd i]; exact sum_congr rfl fun χ _ => mul_comm _ _
    simp only [columnRow_toVec]
    fin_cases a <;> fin_cases c <;>
      simp [lyonsGram, htt, htd, htd', hdd]
  ·
    have hrot : ∀ χ ∈ B, (normalizedColumnRow dt d χ).rotate = normalizedColumnRow dt d (τ χ) := by
      intro χ hχ
      have hrow : columnRow dt d (τ χ) = (columnRow dt d χ).rotate := by
        simp only [columnRow, LyonsRow.rotate, hτt χ hχ, hτd χ hχ]
        rfl
      unfold normalizedColumnRow
      rw [hrow, LyonsRow.fourierSum_rotate]
      split_ifs
      · rfl
      · exact LyonsRow.rotate_neg _
    have hτval : B.val.map τ = B.val := by
      have hmap : B.map τ.toEmbedding = B := by
        ext χ
        simp only [mem_map_equiv]
        rw [← hτB, Equiv.apply_symm_apply]
      have hval := congrArg Finset.val hmap
      rw [map_val] at hval
      exact hval
    rw [hM, Multiset.map_map]
    calc B.val.map (LyonsRow.rotate ∘ normalizedColumnRow dt d)
        = B.val.map (normalizedColumnRow dt d ∘ τ) :=
          Multiset.map_congr rfl fun χ hχ => hrot χ hχ
      _ = (B.val.map τ).map (normalizedColumnRow dt d) := (Multiset.map_map _ _ _).symm
      _ = B.val.map (normalizedColumnRow dt d) := by rw [hτval]
  ·
    have hrow : normalizedColumnRow dt d p = principalRow := by
      have hcol : columnRow dt d p = principalRow := by
        simp only [columnRow, hpt, hpd, principalRow]
        rfl
      unfold normalizedColumnRow
      rw [hcol]
      exact ite_eq_left (by decide)
    rw [← hrow]
    exact Multiset.mem_map_of_mem _ hp

end CFSG.LyonsUnitaryFour
