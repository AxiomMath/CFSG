module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.FiveColumns.SignedDegreeData
public import CFSG.LocalAnalysis.LyonsUnitaryFour.FiveColumns.ColumnConfiguration

public section

open scoped BigOperators

namespace CFSG.LyonsUnitaryFour

variable {ι : Type*}

@[expose] def columnSign (dt : ι → ℤ) (d : Fin 5 → ι → ℤ) (χ : ι) : ℤ :=
  if 0 < (columnRow dt d χ).fourierSum then 1 else -1

theorem columnSign_sq (dt : ι → ℤ) (d : Fin 5 → ι → ℤ) (χ : ι) :
    columnSign dt d χ * columnSign dt d χ = 1 := by
  unfold columnSign; split_ifs <;> norm_num

theorem normalizedColumnRow_toVec (dt : ι → ℤ) (d : Fin 5 → ι → ℤ) (χ : ι) (k : Fin 6) :
    (normalizedColumnRow dt d χ).toVec k = columnSign dt d χ * (columnRow dt d χ).toVec k := by
  unfold normalizedColumnRow columnSign
  split_ifs
  · rw [one_mul]
  · rw [LyonsRow.toVec_neg, neg_one_mul]

theorem normalizedColumnRow_fourierSum (dt : ι → ℤ) (d : Fin 5 → ι → ℤ) (χ : ι) :
    (normalizedColumnRow dt d χ).fourierSum = columnSign dt d χ * ∑ i, d i χ := by
  unfold normalizedColumnRow columnSign
  split_ifs
  · rw [one_mul, columnRow_fourierSum]
  · rw [LyonsRow.fourierSum_neg, neg_one_mul, columnRow_fourierSum]

theorem normalizedColumnRow_fst (dt : ι → ℤ) (d : Fin 5 → ι → ℤ) (χ : ι) :
    (normalizedColumnRow dt d χ).1 = columnSign dt d χ * dt χ := by
  have := normalizedColumnRow_toVec dt d χ 0
  simpa [LyonsRow.toVec, columnRow] using this

theorem signedDegreeData_of_columns [DecidableEq ι] (B : Finset ι) {p : ι} (hp : p ∈ B)
    (dt deg : ι → ℤ)
    (d : Fin 5 → ι → ℤ) (N : ℕ) (P : ℚ)
    (hpt : dt p = 1) (hpd : ∀ i, d i p = if i = 0 then 1 else 0) (hpdeg : deg p = 1)
    (hnz : ∀ χ ∈ B, ∑ i, d i χ ≠ 0) (hdeg_pos : ∀ χ ∈ B, 0 < deg χ)
    (hdeg_ge : ∀ χ ∈ B, χ ≠ p → 12 ≤ deg χ) (hN : 0 < N)
    (hdvd : ∀ χ ∈ B, (deg χ).natAbs ∣ N)
    (hmult : ∀ χ ∈ B, ∃ a b c : ℕ, deg χ = a + 15 * b + 12 * c ∧
      ∑ i, d i χ = a + 15 * b - 4 * c ∧ dt χ = a - b ∧ (χ ≠ p → 1 ≤ c))
    (hdeg_t : ∑ χ ∈ B, deg χ * dt χ = 0) (hdeg_d : ∀ i, ∑ χ ∈ B, deg χ * d i χ = 0)
    (hrec_t : ∑ χ ∈ B, ((∑ i, d i χ : ℤ) : ℚ) ^ 2 * dt χ / deg χ = 0)
    (hrec_d : ∀ i, ∑ χ ∈ B, ((∑ i, d i χ : ℤ) : ℚ) ^ 2 * d i χ / deg χ = P) (hP : 0 < P)
    (τ : ι → ι) (hτ : Set.BijOn τ B B) (hτt : ∀ χ ∈ B, dt (τ χ) = dt χ)
    (hτd : ∀ χ ∈ B, ∀ i, d i (τ χ) = d (3 * i) χ) (hτdeg : ∀ χ ∈ B, deg (τ χ) = deg χ)
    (hprime : ∀ χ ∈ B, χ ≠ p →
      (∀ ψ ∈ B, normalizedColumnRow dt d ψ = normalizedColumnRow dt d χ →
        columnSign dt d ψ * deg ψ = columnSign dt d χ * deg χ → ψ = χ) →
      ∀ q : ℕ, q.Prime → q ∣ N → (q : ℤ) ≤ deg χ + 1) :
    LyonsSignedDegreeData B (normalizedColumnRow dt d) (fun χ => columnSign dt d χ * deg χ) p N
      P := by
  have hsign_abs : ∀ χ, columnSign dt d χ = 1 ∨ columnSign dt d χ = -1 := by
    intro χ; unfold columnSign; split_ifs <;> simp
  have hsignf : ∀ χ ∈ B, Int.sign (columnSign dt d χ * deg χ) = columnSign dt d χ := by
    intro χ hχ
    rcases hsign_abs χ with h | h <;> rw [h]
    · rw [one_mul, Int.sign_eq_one_of_pos (hdeg_pos χ hχ)]
    · rw [neg_one_mul, Int.sign_neg, Int.sign_eq_one_of_pos (hdeg_pos χ hχ)]
  have hfs : ∀ χ, columnSign dt d χ * columnSign dt d χ = 1 := columnSign_sq dt d
  have hpsign : columnSign dt d p = 1 := by
    unfold columnSign
    rw [ite_eq_left]
    rw [columnRow_fourierSum, Fin.sum_univ_five]
    simp [hpd]
  refine
    { principal_mem := hp
      principal_row := ?_
      principal_degree := by rw [hpsign, hpdeg]; rfl
      fourierSum_pos := ?_
      degree_ne_zero := ?_
      degree_ge := ?_
      N_pos := hN
      degree_dvd := ?_
      mult_c_dvd := ?_
      mult_c_nonneg := ?_
      mult_c_pos := ?_
      mult_b_dvd := ?_
      mult_b_nonneg := ?_
      mult_a_dvd := ?_
      mult_a_nonneg := ?_
      degree_eq := ?_
      reciprocal_u := ?_
      reciprocal_v := ?_
      P_pos := hP
      galois := ?_
      prime_bound := ?_ }
  · unfold normalizedColumnRow
    have hcol : columnRow dt d p = principalRow := by
      simp only [columnRow, hpt, hpd, principalRow]
      rfl
    rw [hcol]
    exact ite_eq_left (by decide)
  · intro χ hχ
    rw [normalizedColumnRow_fourierSum]
    unfold columnSign
    rw [columnRow_fourierSum]
    have := hnz χ hχ
    split_ifs with h
    · linarith
    · push Not at h
      have : ∑ i, d i χ < 0 := lt_of_le_of_ne h this
      linarith
  · intro χ hχ
    rcases hsign_abs χ with h | h <;> rw [h] <;> have := hdeg_pos χ hχ <;> omega
  · intro χ hχ hχp
    rcases hsign_abs χ with h | h <;> rw [h] <;> have := hdeg_ge χ hχ hχp
    · rw [one_mul]; exact this.trans (le_abs_self _)
    · rw [neg_one_mul, abs_neg]; exact this.trans (le_abs_self _)
  · intro χ hχ
    rw [Int.natAbs_mul]
    rcases hsign_abs χ with h | h <;> rw [h] <;> simpa using hdvd χ hχ
  · intro χ hχ
    obtain ⟨a, b, c, hd, hs, ht, -⟩ := hmult χ hχ
    rw [normalizedColumnRow_fourierSum, hd, hs]
    exact ⟨columnSign dt d χ * c, by ring⟩
  · intro χ hχ
    obtain ⟨a, b, c, hd, hs, ht, -⟩ := hmult χ hχ
    rw [hsignf χ hχ, normalizedColumnRow_fourierSum]
    have : columnSign dt d χ * (columnSign dt d χ * deg χ - columnSign dt d χ * ∑ i, d i χ) =
        deg χ - ∑ i, d i χ := by
      rw [mul_sub, ← mul_assoc, ← mul_assoc, hfs, one_mul, one_mul]
    rw [this, hd, hs]
    omega
  · intro χ hχ hχp
    obtain ⟨a, b, c, hd, hs, ht, hc⟩ := hmult χ hχ
    have hc1 := hc hχp
    rw [hsignf χ hχ, normalizedColumnRow_fourierSum]
    have : columnSign dt d χ * (columnSign dt d χ * deg χ - columnSign dt d χ * ∑ i, d i χ) =
        deg χ - ∑ i, d i χ := by
      rw [mul_sub, ← mul_assoc, ← mul_assoc, hfs, one_mul, one_mul]
    rw [this, hd, hs]
    omega
  · intro χ hχ
    obtain ⟨a, b, c, hd, hs, ht, -⟩ := hmult χ hχ
    rw [normalizedColumnRow_fourierSum, normalizedColumnRow_fst, hd, hs, ht]
    exact ⟨columnSign dt d χ * b, by ring⟩
  · intro χ hχ
    obtain ⟨a, b, c, hd, hs, ht, -⟩ := hmult χ hχ
    rw [hsignf χ hχ, normalizedColumnRow_fourierSum, normalizedColumnRow_fst]
    have : columnSign dt d χ * (columnSign dt d χ * deg χ + 3 * (columnSign dt d χ *
        ∑ i, d i χ) - 4 * (columnSign dt d χ * dt χ)) =
        deg χ + 3 * ∑ i, d i χ - 4 * dt χ := by
      have := hfs χ
      linear_combination (deg χ + 3 * ∑ i, d i χ - 4 * dt χ) * this
    rw [this, hd, hs, ht]
    omega
  · intro χ hχ
    obtain ⟨a, b, c, hd, hs, ht, -⟩ := hmult χ hχ
    rw [normalizedColumnRow_fourierSum, normalizedColumnRow_fst, hd, hs, ht]
    exact ⟨columnSign dt d χ * a, by ring⟩
  · intro χ hχ
    obtain ⟨a, b, c, hd, hs, ht, -⟩ := hmult χ hχ
    rw [hsignf χ hχ, normalizedColumnRow_fourierSum, normalizedColumnRow_fst]
    have : columnSign dt d χ * (columnSign dt d χ * deg χ + 3 * (columnSign dt d χ *
        ∑ i, d i χ) + 60 * (columnSign dt d χ * dt χ)) =
        deg χ + 3 * ∑ i, d i χ + 60 * dt χ := by
      have := hfs χ
      linear_combination (deg χ + 3 * ∑ i, d i χ + 60 * dt χ) * this
    rw [this, hd, hs, ht]
    omega
  · intro k
    have hterm : ∀ χ, columnSign dt d χ * deg χ * (normalizedColumnRow dt d χ).toVec k =
        deg χ * (columnRow dt d χ).toVec k := by
      intro χ
      rw [normalizedColumnRow_toVec]
      linear_combination (deg χ * (columnRow dt d χ).toVec k) * hfs χ
    simp only [hterm, columnRow_toVec]
    fin_cases k
    · exact hdeg_t
    · exact hdeg_d 0
    · exact hdeg_d 1
    · exact hdeg_d 2
    · exact hdeg_d 4
    · exact hdeg_d 3
  · have hterm : ∀ χ ∈ B, ((normalizedColumnRow dt d χ).fourierSum : ℚ) ^ 2 *
        (normalizedColumnRow dt d χ).1 / ((columnSign dt d χ * deg χ : ℤ) : ℚ) =
        ((∑ i, d i χ : ℤ) : ℚ) ^ 2 * dt χ / deg χ := by
      intro χ hχ
      rw [normalizedColumnRow_fourierSum, normalizedColumnRow_fst]
      have hdeg0 : (deg χ : ℚ) ≠ 0 := by exact_mod_cast (hdeg_pos χ hχ).ne'
      rcases hsign_abs χ with h | h <;> rw [h] <;> push_cast <;> field_simp
    rw [Finset.sum_congr rfl hterm]
    exact hrec_t
  · intro k hk
    have hterm : ∀ χ ∈ B, ((normalizedColumnRow dt d χ).fourierSum : ℚ) ^ 2 *
        (normalizedColumnRow dt d χ).toVec k / ((columnSign dt d χ * deg χ : ℤ) : ℚ) =
        ((∑ i, d i χ : ℤ) : ℚ) ^ 2 * (columnRow dt d χ).toVec k / deg χ := by
      intro χ hχ
      rw [normalizedColumnRow_fourierSum, normalizedColumnRow_toVec]
      have hdeg0 : (deg χ : ℚ) ≠ 0 := by exact_mod_cast (hdeg_pos χ hχ).ne'
      rcases hsign_abs χ with h | h <;> rw [h] <;> push_cast <;> field_simp
    rw [Finset.sum_congr rfl hterm]
    simp only [columnRow_toVec]
    fin_cases k
    · exact absurd rfl hk
    · exact hrec_d 0
    · exact hrec_d 1
    · exact hrec_d 2
    · exact hrec_d 4
    · exact hrec_d 3
  · refine ⟨τ, hτ, fun χ hχ => ⟨?_, ?_⟩⟩
    · have hrow : columnRow dt d (τ χ) = (columnRow dt d χ).rotate := by
        simp only [columnRow, LyonsRow.rotate, hτt χ hχ, hτd χ hχ]
        rfl
      have hsign : columnSign dt d (τ χ) = columnSign dt d χ := by
        unfold columnSign
        rw [hrow, LyonsRow.fourierSum_rotate]
      unfold normalizedColumnRow
      rw [hrow, LyonsRow.fourierSum_rotate]
      split_ifs
      · rfl
      · exact (LyonsRow.rotate_neg _).symm
    · show columnSign dt d (τ χ) * deg (τ χ) = columnSign dt d χ * deg χ
      have hrow : columnRow dt d (τ χ) = (columnRow dt d χ).rotate := by
        simp only [columnRow, LyonsRow.rotate, hτt χ hχ, hτd χ hχ]
        rfl
      have hsign : columnSign dt d (τ χ) = columnSign dt d χ := by
        unfold columnSign
        rw [hrow, LyonsRow.fourierSum_rotate]
      rw [hsign, hτdeg χ hχ]
  · intro χ hχ hχp huniq q hq hqN
    have hbound := hprime χ hχ hχp huniq q hq hqN
    rcases hsign_abs χ with h | h <;> rw [h]
    · rw [one_mul, abs_of_pos (hdeg_pos χ hχ)]; exact hbound
    · rw [neg_one_mul, abs_neg, abs_of_pos (hdeg_pos χ hχ)]; exact hbound

end CFSG.LyonsUnitaryFour
