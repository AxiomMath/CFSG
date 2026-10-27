module

public import CFSG.CharacterTheory.Wreathed.ConditionalFourierParityCore
public import CFSG.Open.LocalVocabulary

public section

open scoped BigOperators

namespace CFSG.Wreathed.ConditionalFirstFourierRows

open CFSG.Wreathed.ConditionalFourier

variable {ι : Type*} [DecidableEq ι] {B : Finset ι} {p : ι}

theorem witness_sub {α : Fin 3 → ι} {β η : Fin 3 → ℤ} {σ : ℤ} {e : Fin 3} (χ : ι)
    (hηe : η e = -β e) (hηi : ∀ i, i ≠ e → η i = β i) (hβe : β e = σ) (φ : ι) :
    (-unitVector p φ + ∑ i, η i * unitVector (α i) φ + 2 * σ * unitVector χ φ) -
      (unitVector p φ + ∑ i, β i * unitVector (α i) φ) =
      -2 * unitVector p φ - 2 * σ * unitVector (α e) φ + 2 * σ * unitVector χ φ := by
  have h : ∑ i, η i * unitVector (α i) φ - ∑ i, β i * unitVector (α i) φ =
      (η e - β e) * unitVector (α e) φ := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single e
      (fun i _ hie => by rw [hηi i hie]; ring) fun h => absurd (Finset.mem_univ e) h]
    ring
  rw [hηe, hβe] at h
  linear_combination h

theorem sum_mul_witness_sub {q χ : ι} (σ : ℤ) (hp : p ∈ B) (hq : q ∈ B) (hχ : χ ∈ B)
    (g : ι → ℤ) :
    ∑ φ ∈ B, g φ * (-2 * unitVector p φ - 2 * σ * unitVector q φ + 2 * σ * unitVector χ φ) =
      -2 * g p - 2 * σ * g q + 2 * σ * g χ := by
  have h : ∀ φ, g φ * (-2 * unitVector p φ - 2 * σ * unitVector q φ + 2 * σ * unitVector χ φ) =
      -2 * (g φ * unitVector p φ) - 2 * σ * (g φ * unitVector q φ) +
        2 * σ * (g φ * unitVector χ φ) := fun φ => by ring
  rw [Finset.sum_congr rfl fun φ _ => h φ, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, sum_mul_unitVector hp,
    sum_mul_unitVector hq, sum_mul_unitVector hχ]

theorem pos_column_eq {y₀ yr cj : ι → ℤ} {q χ : ι} {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) (hp : p ∈ B)
    (hq : q ∈ B) (hχ : χ ∈ B)
    (hdiff : ∀ φ ∈ B, cj φ - y₀ φ =
      -2 * unitVector p φ - 2 * σ * unitVector q φ + 2 * σ * unitVector χ φ)
    (horth : ∑ φ ∈ B, yr φ * cj φ = 0) (h0 : ∑ φ ∈ B, yr φ * y₀ φ = 0) (hyp : yr p = 0) :
    yr χ = yr q := by
  have h : ∑ φ ∈ B, yr φ * (cj φ - y₀ φ) = 0 := by
    rw [Finset.sum_congr rfl fun φ _ => mul_sub (yr φ) (cj φ) (y₀ φ), Finset.sum_sub_distrib,
      horth, h0, sub_zero]
  rw [Finset.sum_congr rfl fun φ hφ => by rw [hdiff φ hφ], sum_mul_witness_sub σ hp hq hχ,
    hyp] at h
  rcases hσ with hs | hs <;> rw [hs] at h <;> linarith only [h]

theorem pos_column_zero_of_four_le {κ : Type*} {J : Finset κ} {yr : ι → ℤ} {χ : κ → ι} {q : ι}
    (hq : q ∈ B) (hχB : ∀ j ∈ J, χ j ∈ B) (hχinj : Set.InjOn χ J) (hχq : ∀ j ∈ J, χ j ≠ q)
    (hJ : 4 ≤ J.card) (hy4 : (B.filter fun φ => yr φ ≠ 0).card = 4)
    (heq : ∀ j ∈ J, yr (χ j) = yr q) : yr q = 0 := by
  by_contra ha
  have hsub : insert q (J.image χ) ⊆ B.filter fun φ => yr φ ≠ 0 := by
    intro φ hφ
    rw [Finset.mem_insert, Finset.mem_image] at hφ
    rw [Finset.mem_filter]
    rcases hφ with rfl | ⟨j, hj, rfl⟩
    · exact ⟨hq, ha⟩
    · exact ⟨hχB j hj, by rw [heq j hj]; exact ha⟩
  have hqJ : q ∉ J.image χ := by
    rw [Finset.mem_image]
    rintro ⟨j, hj, h⟩
    exact hχq j hj h
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hqJ, Finset.card_image_of_injOn hχinj, hy4] at hcard
  omega

theorem even_column_rows {κ : Type*} {J : Finset κ} {y₀ ct : ι → ℤ} {cj : κ → ι → ℤ}
    {χ : κ → ι} {q : ι} {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) (hp : p ∈ B) (hq : q ∈ B)
    (hχB : ∀ j ∈ J, χ j ∈ B) (hχinj : Set.InjOn χ J) (hJ : 2 ≤ J.card) (hqp : q ≠ p)
    (hχp : ∀ j ∈ J, χ j ≠ p) (hχq : ∀ j ∈ J, χ j ≠ q)
    (hdiff : ∀ j ∈ J, ∀ φ ∈ B, cj j φ - y₀ φ =
      -2 * unitVector p φ - 2 * σ * unitVector q φ + 2 * σ * unitVector (χ j) φ)
    (hsq : ∑ φ ∈ B, ct φ * ct φ = 8) (hgram : ∀ j ∈ J, ∑ φ ∈ B, ct φ * cj j φ = 4)
    (horth : ∑ φ ∈ B, ct φ * y₀ φ = 0) (hctp : ct p = -1) (hodd : Odd (ct q)) :
    ct q = -σ ∧ ∀ j ∈ J, ct (χ j) = 0 := by
  have hrel : ∀ j ∈ J, ct (χ j) = ct q + σ := by
    intro j hj
    have h : ∑ φ ∈ B, ct φ * (cj j φ - y₀ φ) = 4 := by
      rw [Finset.sum_congr rfl fun φ _ => mul_sub (ct φ) (cj j φ) (y₀ φ),
        Finset.sum_sub_distrib, hgram j hj, horth, sub_zero]
    rw [Finset.sum_congr rfl fun φ hφ => by rw [hdiff j hj φ hφ],
      sum_mul_witness_sub σ hp hq (hχB j hj), hctp] at h
    rcases hσ with hs | hs <;> rw [hs] at h ⊢ <;> linarith only [h]
  have hle : ct q * ct q ≤ 8 := by
    rw [← hsq]
    exact Finset.single_le_sum (f := fun φ => ct φ * ct φ) (fun φ _ => mul_self_nonneg _) hq
  have hunit : ct q = 1 ∨ ct q = -1 := by
    rw [Int.odd_iff] at hodd
    have h1 : -2 ≤ ct q := by nlinarith
    have h2 : ct q ≤ 2 := by nlinarith
    omega
  have hne : ct q ≠ σ := by
    intro hqσ
    have hpS : p ∉ insert q (J.image χ) := by
      rw [Finset.mem_insert, Finset.mem_image, not_or]
      exact ⟨Ne.symm hqp, fun ⟨j, hj, h⟩ => hχp j hj h⟩
    have hqS : q ∉ J.image χ := by
      rw [Finset.mem_image]
      rintro ⟨j, hj, h⟩
      exact hχq j hj h
    have hsub : insert p (insert q (J.image χ)) ⊆ B := by
      intro φ hφ
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_image] at hφ
      rcases hφ with rfl | rfl | ⟨j, hj, rfl⟩
      · exact hp
      · exact hq
      · exact hχB j hj
    have h4 : ∑ j ∈ J, ct (χ j) * ct (χ j) = ∑ _j ∈ J, (4 : ℤ) :=
      Finset.sum_congr rfl fun j hj => by
        rw [hrel j hj, hqσ]
        rcases hσ with hs | hs <;> rw [hs] <;> norm_num
    have hS : ∑ φ ∈ insert p (insert q (J.image χ)), ct φ * ct φ = 2 + 4 * J.card := by
      rw [Finset.sum_insert hpS, Finset.sum_insert hqS, Finset.sum_image hχinj, h4, hctp, hqσ,
        Finset.sum_const, nsmul_eq_mul]
      rcases hσ with hs | hs <;> rw [hs] <;> ring
    have hle' := Finset.sum_le_sum_of_subset_of_nonneg hsub fun φ _ _ => mul_self_nonneg (ct φ)
    rw [hS, hsq] at hle'
    have hJ' : (2 : ℤ) ≤ J.card := by exact_mod_cast hJ
    linarith only [hle', hJ']
  have hqv : ct q = -σ := by
    rcases hunit with h | h <;> rcases hσ with hs | hs <;> rw [h, hs] at hne ⊢ <;> omega
  exact ⟨hqv, fun j hj => by rw [hrel j hj, hqv]; ring⟩

end CFSG.Wreathed.ConditionalFirstFourierRows
