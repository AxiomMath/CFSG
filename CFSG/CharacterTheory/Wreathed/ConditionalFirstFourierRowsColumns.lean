module

public import CFSG.CharacterTheory.Wreathed.ConditionalFirstFourierRowsTwo

public section

open scoped BigOperators

namespace CFSG.Wreathed.ConditionalFirstFourierRows

open CFSG.Wreathed.ConditionalFourier CFSG.Wreathed.ConditionalOddFourier
  CFSG.Wreathed.ConditionalUniformOddFourier

variable {ι : Type*} [DecidableEq ι] {B : Finset ι} {p : ι} {d : ι → ℤ} {m : ℕ}
  {cc y : ℕ → ι → ℤ} {α : Fin 3 → ι} {β η : Fin 3 → ℤ} {σ : ℤ} {χ : ℕ → ι} {e : Fin 3}

theorem pos_columns_vanish (hm : m = 4 ∨ 8 ≤ m) (hp : p ∈ B) (hdpos : ∀ φ ∈ B, 0 < d φ)
    (hdp : d p = 1)
    (hgram : ∀ t ∈ Finset.Ico 1 m, ∀ s ∈ Finset.Ico 1 m,
      ∑ φ ∈ B, cc t φ * cc s φ = if t = s then 8 else 4)
    (hdeg : ∀ t ∈ Finset.Ico 1 m, ∑ φ ∈ B, d φ * cc t φ = 0)
    (hprin : ∀ t ∈ Finset.Ico 1 m, cc t p = -1)
    (hyval : ∀ r < m / 2, ∀ φ ∈ B, y r φ = 0 ∨ y r φ = 1 ∨ y r φ = -1)
    (hy4 : ∀ r < m / 2, (B.filter fun φ => y r φ ≠ 0).card = 4)
    (hydeg : ∀ r < m / 2, ∑ φ ∈ B, d φ * y r φ = 0)
    (hyp : ∀ r, 0 < r → r < m / 2 → y r p = 0)
    (hygram : ∀ r < m / 2, ∀ s < m / 2, ∑ φ ∈ B, y r φ * y s φ = if r = s then 4 else 0)
    (horth : ∀ r < m / 2, ∀ t ∈ Finset.Ico 1 m, ∑ φ ∈ B, y r φ * cc t φ = 0)
    (hσ : σ = 1 ∨ σ = -1) (hαinj : Function.Injective α) (hα : ∀ i, α i ∈ B ∧ α i ≠ p)
    (hβ : ∀ i, β i = 1 ∨ β i = -1) (hχinj : Set.InjOn χ ((Finset.Ico 1 m).filter Odd))
    (hχ : ∀ j ∈ (Finset.Ico 1 m).filter Odd, χ j ∈ B ∧ χ j ≠ p ∧ ∀ i, χ j ≠ α i)
    (hχdeg : ∀ j ∈ (Finset.Ico 1 m).filter Odd, ∀ t ∈ (Finset.Ico 1 m).filter Odd,
      d (χ j) = d (χ t))
    (hηe : η e = -β e) (hηi : ∀ i, i ≠ e → η i = β i) (hβe : β e = σ)
    (hy0 : ∀ φ ∈ B, y 0 φ = unitVector p φ + ∑ i, β i * unitVector (α i) φ)
    (hcj : ∀ j ∈ (Finset.Ico 1 m).filter Odd, ∀ φ ∈ B, cc j φ =
      -unitVector p φ + ∑ i, η i * unitVector (α i) φ + 2 * σ * unitVector (χ j) φ)
    (hJcard : ((Finset.Ico 1 m).filter Odd).card = m / 2) :
    ∀ r, 0 < r → r < m / 2 →
      y r (α e) = 0 ∧ ∀ j ∈ (Finset.Ico 1 m).filter Odd, y r (χ j) = 0 := by
  have hJI : ∀ j ∈ (Finset.Ico 1 m).filter Odd, j ∈ Finset.Ico 1 m :=
    fun j hj => (Finset.mem_filter.mp hj).1
  have hdiff : ∀ j ∈ (Finset.Ico 1 m).filter Odd, ∀ φ ∈ B, cc j φ - y 0 φ =
      -2 * unitVector p φ - 2 * σ * unitVector (α e) φ + 2 * σ * unitVector (χ j) φ := by
    intro j hj φ hφ
    rw [hcj j hj φ hφ, hy0 φ hφ]
    exact witness_sub (χ j) hηe hηi hβe φ
  intro r hr0 hrM
  have h0M : 0 < m / 2 := by omega
  have heq : ∀ j ∈ (Finset.Ico 1 m).filter Odd, y r (χ j) = y r (α e) := by
    intro j hj
    refine pos_column_eq hσ hp (hα e).1 (hχ j hj).1 (hdiff j hj) (horth r hrM j (hJI j hj)) ?_
      (hyp r hr0 hrM)
    rw [hygram r hrM 0 h0M, ite_eq_right (by omega)]
  have hzero : y r (α e) = 0 := by
    rcases hm with hm4 | hm8
    · subst hm4
      have hr1 : r = 1 := by omega
      subst hr1
      have h1 : (1 : ℕ) ∈ (Finset.Ico 1 4).filter Odd := by decide
      have h3 : (3 : ℕ) ∈ (Finset.Ico 1 4).filter Odd := by decide
      have h2I : (2 : ℕ) ∈ Finset.Ico 1 4 := by decide
      have h13 : χ 1 ≠ χ 3 := fun h => by
        have := hχinj h1 h3 h
        omega
      have hflip : ∀ s ∈ Finset.Ico 1 4, ∀ q < 4 / 2,
          ∑ φ ∈ B, cc s φ * y q φ = 0 := by
        intro s hs q hq
        rw [← horth q hq s hs]
        exact Finset.sum_congr rfl fun φ _ => mul_comm _ _
      exact two_pos_column_zero hσ hp hαinj hα hβ hβe (hχ 1 h1).1 (hχ 3 h3).1 (hχ 1 h1).2.1
        (hχ 3 h3).2.1 (hχ 1 h1).2.2 (hχ 3 h3).2.2 h13 hdpos hdp (hχdeg 3 h3 1 h1) hy0
        (hydeg 0 (by norm_num)) (hyval 1 (by norm_num)) (hy4 1 (by norm_num))
        (hyp 1 one_pos (by norm_num))
        (by rw [hygram 0 (by norm_num) 1 (by norm_num), ite_eq_right (by norm_num)])
        (hydeg 1 (by norm_num)) (heq 1 h1) (heq 3 h3) (hdiff 1 h1) (hdiff 3 h3)
        (by rw [hgram 2 h2I 2 h2I, ite_eq_left rfl])
        (by rw [hgram 2 h2I 1 (by decide), ite_eq_right (by norm_num)])
        (by rw [hgram 2 h2I 3 (by decide), ite_eq_right (by norm_num)])
        (hprin 2 h2I) (hflip 2 h2I 0 (by norm_num)) (hflip 2 h2I 1 (by norm_num)) (hdeg 2 h2I)
    · exact pos_column_zero_of_four_le (hα e).1 (fun j hj => (hχ j hj).1) hχinj
        (fun j hj => (hχ j hj).2.2 e) (by omega) (hy4 r hrM) heq
  exact ⟨hzero, fun j hj => (heq j hj).trans hzero⟩

theorem first_rows_columns (hp : p ∈ B)
    (hgram : ∀ t ∈ Finset.Ico 1 m, ∀ s ∈ Finset.Ico 1 m,
      ∑ φ ∈ B, cc t φ * cc s φ = if t = s then 8 else 4)
    (hprin : ∀ t ∈ Finset.Ico 1 m, cc t p = -1)
    (horth : ∀ r < m / 2, ∀ t ∈ Finset.Ico 1 m, ∑ φ ∈ B, y r φ * cc t φ = 0)
    (hσ : σ = 1 ∨ σ = -1) (hαinj : Function.Injective α) (hα : ∀ i, α i ∈ B ∧ α i ≠ p)
    (hχinj : Set.InjOn χ ((Finset.Ico 1 m).filter Odd))
    (hχ : ∀ j ∈ (Finset.Ico 1 m).filter Odd, χ j ∈ B ∧ χ j ≠ p ∧ ∀ i, χ j ≠ α i)
    (hηe : η e = -β e) (hηi : ∀ i, i ≠ e → η i = β i) (hβe : β e = σ)
    (hy0 : ∀ φ ∈ B, y 0 φ = unitVector p φ + ∑ i, β i * unitVector (α i) φ)
    (hcj : ∀ j ∈ (Finset.Ico 1 m).filter Odd, ∀ φ ∈ B, cc j φ =
      -unitVector p φ + ∑ i, η i * unitVector (α i) φ + 2 * σ * unitVector (χ j) φ)
    (hJ2 : 2 ≤ ((Finset.Ico 1 m).filter Odd).card)
    (hpos : ∀ r, 0 < r → r < m / 2 →
      y r (α e) = 0 ∧ ∀ j ∈ (Finset.Ico 1 m).filter Odd, y r (χ j) = 0)
    (hpar : ∀ t ∈ Finset.Ico 1 m, Even t →
      ∃ r, 0 < r ∧ r < m / 2 ∧ ∀ φ ∈ B, cc t φ ≡ y 0 φ + y r φ [ZMOD 2]) :
    ∀ t ∈ Finset.Ico 1 m, cc t (α e) = -σ ∧
      ∀ j ∈ (Finset.Ico 1 m).filter Odd, cc t (χ j) = if t = j then 2 * σ else 0 := by
  have hJI : ∀ j ∈ (Finset.Ico 1 m).filter Odd, j ∈ Finset.Ico 1 m :=
    fun j hj => (Finset.mem_filter.mp hj).1
  have hdiff : ∀ j ∈ (Finset.Ico 1 m).filter Odd, ∀ φ ∈ B, cc j φ - y 0 φ =
      -2 * unitVector p φ - 2 * σ * unitVector (α e) φ + 2 * σ * unitVector (χ j) φ := by
    intro j hj φ hφ
    rw [hcj j hj φ hφ, hy0 φ hφ]
    exact witness_sub (χ j) hηe hηi hβe φ
  have hy0α : y 0 (α e) = σ := by
    rw [hy0 (α e) (hα e).1, unitVector_of_ne (hα e).2, sum_mul_unitVector_apply hαinj, hβe]
    ring
  intro t ht
  by_cases hto : Odd t
  · have htJ : t ∈ (Finset.Ico 1 m).filter Odd := Finset.mem_filter.mpr ⟨ht, hto⟩
    refine ⟨?_, fun j hj => ?_⟩
    · rw [hcj t htJ (α e) (hα e).1, unitVector_of_ne (hα e).2, sum_mul_unitVector_apply hαinj,
        unitVector_of_ne fun h => (hχ t htJ).2.2 e h.symm, hηe, hβe]
      ring
    · rw [hcj t htJ (χ j) (hχ j hj).1, unitVector_of_ne (hχ j hj).2.1,
        sum_mul_unitVector_of_forall_ne η (hχ j hj).2.2]
      by_cases htj : t = j
      · rw [htj, unitVector_self, ite_eq_left rfl]
        ring
      · rw [unitVector_of_ne fun h => htj (hχinj hj htJ h).symm, ite_eq_right htj]
        ring
  · have hte : Even t := Nat.not_odd_iff_even.mp hto
    have h0M : 0 < m / 2 := by
      have := Finset.card_le_card (Finset.filter_subset Odd (Finset.Ico 1 m))
      rw [Nat.card_Ico] at this
      omega
    obtain ⟨r, hr0, hrM, hpr⟩ := hpar t ht hte
    have hodd : Odd (cc t (α e)) := by
      have h := hpr (α e) (hα e).1
      rw [hy0α, (hpos r hr0 hrM).1, add_zero] at h
      unfold Int.ModEq at h
      rw [Int.odd_iff]
      rcases hσ with hs | hs <;> rw [hs] at h <;> omega
    have hne : ∀ j ∈ (Finset.Ico 1 m).filter Odd, t ≠ j := fun j hj h =>
      hto (by rw [h]; exact (Finset.mem_filter.mp hj).2)
    have hgt : ∀ j ∈ (Finset.Ico 1 m).filter Odd, ∑ φ ∈ B, cc t φ * cc j φ = 4 := by
      intro j hj
      rw [hgram t ht j (hJI j hj), ite_eq_right (hne j hj)]
    have hot : ∑ φ ∈ B, cc t φ * y 0 φ = 0 := by
      rw [← horth 0 h0M t ht]
      exact Finset.sum_congr rfl fun φ _ => mul_comm _ _
    obtain ⟨h1, h2⟩ := even_column_rows hσ hp (hα e).1 (fun j hj => (hχ j hj).1) hχinj hJ2
      (hα e).2 (fun j hj => (hχ j hj).2.1) (fun j hj => (hχ j hj).2.2 e) hdiff
      (by rw [hgram t ht t ht, ite_eq_left rfl]) hgt hot (hprin t ht) hodd
    exact ⟨h1, fun j hj => by rw [h2 j hj, ite_eq_right (hne j hj)]⟩

end CFSG.Wreathed.ConditionalFirstFourierRows
