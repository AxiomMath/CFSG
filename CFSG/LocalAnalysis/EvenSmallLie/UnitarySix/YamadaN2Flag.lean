module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2FlagData
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2F4

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaN2

open Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar

@[expose] def FlagM (φ : Mat18) : Prop :=
  ∀ r c : Fin 18, ¬ ((clsN r ≤ 1 ∧ clsN c = 2) ∨ (clsN r = 0 ∧ clsN c = 1)) → φ r c = 0

@[expose] def RowV1 (Δ : Mat18) : Prop := ∀ r c : Fin 18, clsN r ≠ 0 → Δ r c = 0

@[expose] def ColNV1 (Δ : Mat18) : Prop := ∀ r c : Fin 18, clsN c = 0 → Δ r c = 0

@[expose] def FixV1 (Y : Mat18) : Prop := ∀ r k : Fin 18, clsN k = 0 → Y r k = (1 : Mat18) r k

@[expose] def PresV1 (T : Mat18) : Prop := ∀ r k : Fin 18, clsN k = 0 → clsN r ≠ 0 → T r k = 0

theorem fixV1_mul_rowV1 {Y Δ : Mat18} (hY : FixV1 Y) (hΔ : RowV1 Δ) : Y * Δ = Δ := by
  ext r c
  rw [mul_apply]
  rw [Finset.sum_eq_single r]
  · by_cases hr : clsN r = 0
    · rw [hY r r hr, one_apply_eq, one_mul]
    · rw [hΔ r c hr, mul_zero]
  · intro k _ hkr
    by_cases hk : clsN k = 0
    · rw [hY r k hk, one_apply_ne (Ne.symm hkr), zero_mul]
    · rw [hΔ k c hk, mul_zero]
  · intro h; exact absurd (Finset.mem_univ r) h

theorem colNV1_mul_rowV1 {Δ Δ' : Mat18} (hΔ : ColNV1 Δ) (hΔ' : RowV1 Δ') : Δ * Δ' = 0 := by
  ext r c
  rw [mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : clsN k = 0
  · rw [hΔ r k hk, zero_mul]
  · rw [hΔ' k c hk, mul_zero]

theorem rowV1_mul {Δ : Mat18} (hΔ : RowV1 Δ) (M : Mat18) : RowV1 (Δ * M) := by
  intro r c hr
  rw [mul_apply]
  exact Finset.sum_eq_zero fun k _ => by rw [hΔ r k hr, zero_mul]

theorem presV1_mul_rowV1 {T Δ : Mat18} (hT : PresV1 T) (hΔ : RowV1 Δ) : RowV1 (T * Δ) := by
  intro r c hr
  rw [mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : clsN k = 0
  · rw [hT r k hk hr, zero_mul]
  · rw [hΔ k c hk, mul_zero]

theorem flagM_mul_flagM {φ ψ : Mat18} (hφ : FlagM φ) (hψ : FlagM ψ) (r c : Fin 18)
    (h : ¬ (clsN r = 0 ∧ clsN c = 2)) : (φ * ψ) r c = 0 := by
  rw [mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases h1 : (clsN r ≤ 1 ∧ clsN k = 2) ∨ (clsN r = 0 ∧ clsN k = 1)
  · by_cases h2 : (clsN k ≤ 1 ∧ clsN c = 2) ∨ (clsN k = 0 ∧ clsN c = 1)
    · exfalso
      rcases h1 with ⟨_, hk⟩ | ⟨hr, hk⟩ <;> rcases h2 with ⟨hk', hc⟩ | ⟨hk', _⟩ <;> omega
    · rw [hψ k c h2, mul_zero]
  · rw [hφ r k h1, zero_mul]

theorem beq_fin_iff {n : ℕ} (r k : Fin n) : ((r : ℕ) == (k : ℕ)) = true ↔ r = k := by
  rw [beq_iff_eq, Fin.val_inj]

theorem one_apply_eq_bz {n : ℕ} (r k : Fin n) : (1 : Matrix (Fin n) (Fin n) (ZMod 2)) r k =
    bz ((r : ℕ) == (k : ℕ)) := by
  by_cases h : r = k
  · subst h; simp
  · rw [one_apply_ne h]
    have : ((r : ℕ) == (k : ℕ)) = false := by
      rw [Bool.eq_false_iff]; intro h'; exact h ((beq_fin_iff r k).mp h')
    rw [this, bz_false]

theorem presV1_of {A : Array ℕ} (h : presV1B A = true) : PresV1 (toMat 18 18 A) := by
  intro r k hk hr
  simp only [presV1B, List.all_eq_true, List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq,
    beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  rcases h r r.isLt k k.isLt with (h1 | h1) | h1
  · exact absurd hk h1
  · exact absurd h1 hr
  · rw [toMat_apply, h1, bz_false]

theorem triB_apply {A : Array ℕ} (h : triB A = true) (r c : Fin 18) (hrc : clsN c < clsN r) :
    toMat 18 18 A r c = 0 := by
  simp only [triB, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true, decide_eq_false_iff_not, not_lt] at h
  rcases h r r.isLt c c.isLt with h1 | h1
  · omega
  · rw [toMat_apply, h1, bz_false]

theorem bdiagB_apply {A : Array ℕ} (h : bdiagB A = true) (r c : Fin 18) (hrc : clsN c ≠ clsN r) :
    toMat 18 18 A r c = 0 := by
  simp only [bdiagB, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    Bool.not_eq_eq_eq_not, Bool.not_true] at h
  rcases h r r.isLt c c.isLt with h1 | h1
  · exact absurd h1 hrc
  · rw [toMat_apply, h1, bz_false]

theorem lay1B_apply {A : Array ℕ} (h : lay1B A = true) (r c : Fin 18)
    (hrc : ¬ (clsN r = 1 ∧ clsN c = 2)) : toMat 18 18 A r c = (1 : Mat18) r c := by
  simp only [lay1B, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq] at h
  rcases h r r.isLt c c.isLt with h1 | h1
  · exact absurd h1 hrc
  · rw [toMat_apply, one_apply_eq_bz, h1]

theorem fixV1_of_lay1B {A : Array ℕ} (h : lay1B A = true) : FixV1 (toMat 18 18 A) := by
  intro r k hk
  exact lay1B_apply h r k (fun h' => by omega)

theorem w0pC_lt (i : Fin 8) : w0pC i < 18 := by revert i; decide

theorem w1C_lt (j : Fin 8) : w1C j < 18 := by revert j; decide

@[expose] def w0pF (i : Fin 8) : Fin 18 := ⟨w0pC i, w0pC_lt i⟩

@[expose] def w1F (j : Fin 8) : Fin 18 := ⟨w1C j, w1C_lt j⟩

theorem w0pF_injective : Function.Injective w0pF := by
  intro i i' h; revert i i'; decide

theorem w1F_injective : Function.Injective w1F := by
  intro j j' h; revert j j'; decide

theorem clsN_w0pF (i : Fin 8) : clsN (w0pF i) = 1 := by revert i; decide

theorem clsN_w1F (j : Fin 8) : clsN (w1F j) = 2 := by revert j; decide

theorem exists_w0pF {k : Fin 18} (hk : clsN k = 1) : ∃ i, w0pF i = k := by
  revert k; decide

theorem exists_w1F {k : Fin 18} (hk : clsN k = 2) : ∃ j, w1F j = k := by
  revert k; decide

theorem clsN_le (k : Fin 18) : clsN k ≤ 2 := by revert k; decide

theorem sum_fin18 {R : Type*} [AddCommMonoid R] (f : Fin 18 → R) (e : Fin 8 → Fin 18)
    (he : Function.Injective e) (hf : ∀ k, (∀ i, e i ≠ k) → f k = 0) :
    ∑ k, f k = ∑ i, f (e i) := by
  rw [← Finset.sum_image (s := Finset.univ) (g := e) (fun x _ y _ h => he h)]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun k _ hk => hf k fun i hi => hk ?_
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩

@[expose] def blk1M (M : Mat18) : Mat8 := Matrix.of fun i j => M (w0pF i) (w1F j)

@[expose] def sub0M (M : Mat18) : Mat8 := Matrix.of fun i j => M (w0pF i) (w0pF j)

@[expose] def sub1M (M : Mat18) : Mat8 := Matrix.of fun i j => M (w1F i) (w1F j)

theorem blk1M_add (M N : Mat18) : blk1M (M + N) = blk1M M + blk1M N := by
  ext i j; simp [blk1M]

theorem blk1M_one : blk1M 1 = 0 := by
  ext i j
  simp only [blk1M, Matrix.of_apply, Matrix.zero_apply]
  rw [one_apply_ne]
  intro h
  have := clsN_w0pF i
  rw [h, clsN_w1F] at this
  exact absurd this (by norm_num)

theorem blk1M_flag_mul {φ ψ : Mat18} (hφ : FlagM φ) (hψ : FlagM ψ) : blk1M (φ * ψ) = 0 := by
  ext i j
  simp only [blk1M, Matrix.of_apply, Matrix.zero_apply]
  refine flagM_mul_flagM hφ hψ _ _ fun h => ?_
  have := clsN_w0pF i
  omega

theorem blk1M_mul_flag {φ ψ : Mat18} (hφ : FlagM φ) (hψ : FlagM ψ) :
    blk1M ((1 + φ) * (1 + ψ)) = blk1M (1 + φ) + blk1M (1 + ψ) := by
  rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul]
  simp only [blk1M_add, blk1M_flag_mul hφ hψ, blk1M_one]
  abel

theorem blk1M_tri_conj {V φ : Mat18} (hV : ∀ r c : Fin 18, clsN c < clsN r → V r c = 0)
    (hφ : FlagM φ) : blk1M (V * φ * V) = sub0M V * blk1M φ * sub1M V := by
  ext i j
  simp only [blk1M, sub0M, sub1M, Matrix.of_apply, mul_apply]
  have hin : ∀ l : Fin 18, (∑ k, V (w0pF i) k * φ k l) =
      ∑ k', V (w0pF i) (w0pF k') * φ (w0pF k') l := fun l => by
    refine sum_fin18 (fun k => V (w0pF i) k * φ k l) w0pF w0pF_injective fun k hk => ?_
    have hk1 : clsN k ≠ 1 := fun h => by obtain ⟨i', hi'⟩ := exists_w0pF h; exact hk i' hi'
    by_cases h0 : clsN k = 0
    · rw [hV (w0pF i) k (by rw [clsN_w0pF]; omega), zero_mul]
    · have := clsN_le k
      rw [hφ k l (by omega), mul_zero]
  simp only [hin]
  refine sum_fin18 (fun l => (∑ k', V (w0pF i) (w0pF k') * φ (w0pF k') l) * V l (w1F j)) w1F
    w1F_injective fun l hl => ?_
  have hl2 : clsN l ≠ 2 := fun h => by obtain ⟨j', hj'⟩ := exists_w1F h; exact hl j' hj'
  have h0 : ∑ k', V (w0pF i) (w0pF k') * φ (w0pF k') l = 0 :=
    Finset.sum_eq_zero fun k' _ => by
      rw [hφ (w0pF k') l (by rw [clsN_w0pF]; omega), mul_zero]
  simp only [h0, zero_mul]

theorem blk1M_toMat (A : Array ℕ) : blk1M (toMat 18 18 A) = toMat 8 8 (blk1Bits A) := by
  ext i j
  simp only [blk1M, Matrix.of_apply, toMat_apply, blk1Bits, getD_ofFn, testBit_bitsOf, j.isLt,
    decide_true, Bool.true_and]
  rfl

theorem subBits_apply (rr cc : ℕ → ℕ) (A : Array ℕ) (i j : Fin 8) :
    toMat 8 8 (subBits rr cc A) i j = bz ((A.getD (rr i) 0).testBit (cc j)) := by
  simp only [toMat_apply, subBits, getD_ofFn, testBit_bitsOf, j.isLt, decide_true, Bool.true_and]

theorem sub0M_toMat (A : Array ℕ) : sub0M (toMat 18 18 A) = toMat 8 8 (subBits w0pC w0pC A) := by
  ext i j
  rw [subBits_apply]
  rfl

theorem sub1M_toMat (A : Array ℕ) : sub1M (toMat 18 18 A) = toMat 8 8 (subBits w1C w1C A) := by
  ext i j
  rw [subBits_apply]
  rfl

end CFSG.EvenSmallLie.UnitarySix.YamadaN2
