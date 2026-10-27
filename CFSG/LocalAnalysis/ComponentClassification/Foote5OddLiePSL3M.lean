module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLiePSL3H

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open CFSG Subgroup Matrix
open CFSG.ClassicalInvolution.Balance.StrongBalance.Linear
open scoped MatrixGroups

variable {k : Type} [Field k] {n : ℕ}

theorem block_scalar_of_transvections {B : Matrix (Fin n) (Fin n) k} {J : Finset (Fin n)}
    (hJ : 2 ≤ J.card)
    (h : ∀ i ∈ J, ∀ j ∈ J, ∀ hij : i ≠ j,
      B * (SpecialLinearGroup.transvection hij (1 : k) : Matrix (Fin n) (Fin n) k) =
        (SpecialLinearGroup.transvection hij (1 : k) : Matrix (Fin n) (Fin n) k) * B) :
    ∃ c : k, ∀ a b, (a ∈ J ∨ b ∈ J) → B a b = if a = b then c else 0 := by
  have hs : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → B * single i j (1 : k) = single i j (1 : k) * B := by
    intro i hi j hj hij
    have h1 := h i hi j hj hij
    rw [SpecialLinearGroup.transvection_coe, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      Matrix.one_mul] at h1
    exact add_left_cancel h1
  have hne : ∀ i ∈ J, ∃ j ∈ J, j ≠ i := fun i _ => Finset.exists_mem_ne (by omega) i
  have hcol : ∀ i ∈ J, ∀ a, a ≠ i → B a i = 0 := by
    intro i hi a ha
    obtain ⟨j, hj, hji⟩ := hne i hi
    have h1 := congrFun (congrFun (hs i hi j hj hji.symm) a) j
    rw [mul_single_apply_same, single_mul_apply_of_ne (h := ha), mul_one] at h1
    exact h1
  have hrow : ∀ j ∈ J, ∀ b, b ≠ j → B j b = 0 := by
    intro j hj b hb
    obtain ⟨i, hi, hij⟩ := hne j hj
    have h1 := congrFun (congrFun (hs i hi j hj hij) i) b
    rw [mul_single_apply_of_ne (hbj := hb), single_mul_apply_same, one_mul] at h1
    exact h1.symm
  have hdiag : ∀ i ∈ J, ∀ j ∈ J, B i i = B j j := by
    intro i hi j hj
    by_cases hij : i = j
    · rw [hij]
    · have h1 := congrFun (congrFun (hs i hi j hj hij) i) j
      rw [mul_single_apply_same, single_mul_apply_same, mul_one, one_mul] at h1
      exact h1
  obtain ⟨j₀, hj₀⟩ : J.Nonempty := Finset.card_pos.mp (by omega)
  refine ⟨B j₀ j₀, fun a b hab => ?_⟩
  by_cases h' : a = b
  · subst h'
    rw [ite_eq_left rfl]
    exact hdiag a (hab.elim id id) j₀ hj₀
  · rw [ite_eq_right h']
    rcases hab with ha | hb
    · exact hrow a ha b (Ne.symm h')
    · exact hcol b hb a h'

section Two

variable {J : Finset (Fin n)} (hJ : J.card = 2)

theorem mul_blockTwo_apply_pt (B : Matrix (Fin n) (Fin n) k) (X : SL(2, k)) (a : Fin n)
    (β : Fin 2) :
    (B * (blockTwo J hJ X : Matrix (Fin n) (Fin n) k)) a (blockPt J hJ β) =
      B a (blockPt J hJ 0) * (X : Matrix (Fin 2) (Fin 2) k) 0 β +
        B a (blockPt J hJ 1) * (X : Matrix (Fin 2) (Fin 2) k) 1 β := by
  have hne : blockPt J hJ 0 ≠ blockPt J hJ 1 := fun h =>
    absurd (blockPt_injective J hJ h) (by decide)
  rw [Matrix.mul_apply, Fintype.sum_eq_add _ _ hne, blockTwo_apply_pt, blockTwo_apply_pt]
  rintro c ⟨hc0, hc1⟩
  have hcJ : c ∉ J := fun hc => (eq_blockPt_of_mem J hJ hc).elim hc0 hc1
  rw [blockTwo_apply_not_mem J hJ X (Or.inl hcJ),
    ite_eq_right (fun h => hcJ (by rw [h]; exact blockPt_mem J hJ β)), mul_zero]

theorem mul_blockTwo_apply_not_mem (B : Matrix (Fin n) (Fin n) k) (X : SL(2, k)) (a : Fin n)
    {b : Fin n} (hb : b ∉ J) :
    (B * (blockTwo J hJ X : Matrix (Fin n) (Fin n) k)) a b = B a b := by
  rw [Matrix.mul_apply, Fintype.sum_eq_single b, blockTwo_apply_not_mem J hJ X (Or.inr hb),
    ite_eq_left rfl, mul_one]
  intro c hc
  rw [blockTwo_apply_not_mem J hJ X (Or.inr hb), ite_eq_right hc, mul_zero]

theorem blockTwo_mul_apply_pt (B : Matrix (Fin n) (Fin n) k) (X : SL(2, k)) (α : Fin 2)
    (b : Fin n) :
    ((blockTwo J hJ X : Matrix (Fin n) (Fin n) k) * B) (blockPt J hJ α) b =
      (X : Matrix (Fin 2) (Fin 2) k) α 0 * B (blockPt J hJ 0) b +
        (X : Matrix (Fin 2) (Fin 2) k) α 1 * B (blockPt J hJ 1) b := by
  have hne : blockPt J hJ 0 ≠ blockPt J hJ 1 := fun h =>
    absurd (blockPt_injective J hJ h) (by decide)
  rw [Matrix.mul_apply, Fintype.sum_eq_add _ _ hne, blockTwo_apply_pt, blockTwo_apply_pt]
  rintro c ⟨hc0, hc1⟩
  have hcJ : c ∉ J := fun hc => (eq_blockPt_of_mem J hJ hc).elim hc0 hc1
  rw [blockTwo_apply_not_mem J hJ X (Or.inr hcJ),
    ite_eq_right (fun h => hcJ (by rw [← h]; exact blockPt_mem J hJ α)), zero_mul]

theorem blockTwo_mul_apply_not_mem (B : Matrix (Fin n) (Fin n) k) (X : SL(2, k)) {a : Fin n}
    (ha : a ∉ J) (b : Fin n) :
    ((blockTwo J hJ X : Matrix (Fin n) (Fin n) k) * B) a b = B a b := by
  rw [Matrix.mul_apply, Fintype.sum_eq_single a, blockTwo_apply_not_mem J hJ X (Or.inl ha),
    ite_eq_left rfl, one_mul]
  intro c hc
  rw [blockTwo_apply_not_mem J hJ X (Or.inl ha), ite_eq_right (Ne.symm hc), zero_mul]

theorem block_scalar_of_two (h2 : (2 : k) ≠ 0) {B : Matrix (Fin n) (Fin n) k}
    (h₁ : B * (blockTwo J hJ (qOne k) : Matrix (Fin n) (Fin n) k) =
      (blockTwo J hJ (qOne k) : Matrix (Fin n) (Fin n) k) * B)
    (h₂ : B * (blockTwo J hJ (qTwo k) : Matrix (Fin n) (Fin n) k) =
      (blockTwo J hJ (qTwo k) : Matrix (Fin n) (Fin n) k) * B) :
    ∃ c : k, ∀ a b, (a ∈ J ∨ b ∈ J) → B a b = if a = b then c else 0 := by
  set j₀ := blockPt J hJ 0 with hj₀
  set j₁ := blockPt J hJ 1 with hj₁
  have hne : j₀ ≠ j₁ := fun h => absurd (blockPt_injective J hJ h) (by decide)
  have e₁ := fun a b => congrFun (congrFun h₁ a) b
  have e₂ := fun a b => congrFun (congrFun h₂ a) b
  have hq1 : ∀ α β, (qOne k : Matrix (Fin 2) (Fin 2) k) α β = !![0, 1; -1, 0] α β :=
    fun _ _ => rfl
  have hq2 : ∀ α β, (qTwo k : Matrix (Fin 2) (Fin 2) k) α β = !![1, 1; 1, 2] α β :=
    fun _ _ => rfl
  have hcancel : ∀ x : k, x = -x → x = 0 := by
    intro x hx
    have : (2 : k) * x = 0 := by linear_combination hx
    exact (mul_eq_zero.mp this).resolve_left h2
  have hcolJ : ∀ a, a ∉ J → B a j₀ = 0 ∧ B a j₁ = 0 := by
    intro a ha
    have h0 := e₁ a j₀
    have h1 := e₁ a j₁
    rw [hj₀, mul_blockTwo_apply_pt, blockTwo_mul_apply_not_mem _ _ _ ha] at h0
    rw [hj₁, mul_blockTwo_apply_pt, blockTwo_mul_apply_not_mem _ _ _ ha] at h1
    simp only [hq1, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
      cons_val_fin_one, mul_zero, mul_one, zero_add, add_zero, mul_neg] at h0 h1
    have hx : B a (blockPt J hJ 0) = 0 := hcancel _ (by linear_combination h1 - h0)
    exact ⟨hx, by rw [← h1]; exact hx⟩
  have hrowJ : ∀ b, b ∉ J → B j₀ b = 0 ∧ B j₁ b = 0 := by
    intro b hb
    have h0 := e₁ j₀ b
    have h1 := e₁ j₁ b
    rw [hj₀, mul_blockTwo_apply_not_mem _ _ _ _ hb, blockTwo_mul_apply_pt] at h0
    rw [hj₁, mul_blockTwo_apply_not_mem _ _ _ _ hb, blockTwo_mul_apply_pt] at h1
    simp only [hq1, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
      cons_val_fin_one, zero_mul, one_mul, zero_add, add_zero, neg_mul] at h0 h1
    have hx : B (blockPt J hJ 0) b = 0 := hcancel _ (by linear_combination h0 + h1)
    exact ⟨hx, by rw [← h0]; exact hx⟩
  have hd : B j₀ j₀ = B j₁ j₁ ∧ B j₀ j₁ = 0 ∧ B j₁ j₀ = 0 := by
    have h00 := e₁ j₀ j₀
    have h01 := e₁ j₀ j₁
    have g00 := e₂ j₀ j₀
    rw [hj₀, mul_blockTwo_apply_pt, blockTwo_mul_apply_pt] at h00 g00
    rw [hj₀, hj₁, mul_blockTwo_apply_pt, blockTwo_mul_apply_pt] at h01
    simp only [hq1, hq2, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
      cons_val_fin_one, zero_mul, one_mul, mul_zero, mul_one, zero_add, add_zero,
      mul_neg] at h00 h01 g00
    have hx : B (blockPt J hJ 0) (blockPt J hJ 1) = 0 :=
      hcancel _ (by linear_combination g00 - h00)
    refine ⟨h01, hx, ?_⟩
    linear_combination -h00 - hx
  refine ⟨B j₀ j₀, fun a b hab => ?_⟩
  by_cases haJ : a ∈ J <;> by_cases hbJ : b ∈ J
  · rcases eq_blockPt_of_mem J hJ haJ with rfl | rfl <;>
      rcases eq_blockPt_of_mem J hJ hbJ with rfl | rfl
    · rw [ite_eq_left rfl]
    · rw [ite_eq_right hne]
      exact hd.2.1
    · rw [ite_eq_right hne.symm]
      exact hd.2.2
    · rw [ite_eq_left rfl]
      exact hd.1.symm
  · rw [ite_eq_right (fun h : a = b => hbJ (by rw [← h]; exact haJ))]
    rcases eq_blockPt_of_mem J hJ haJ with rfl | rfl
    · exact (hrowJ b hbJ).1
    · exact (hrowJ b hbJ).2
  · rw [ite_eq_right (fun h : a = b => haJ (by rw [h]; exact hbJ))]
    rcases eq_blockPt_of_mem J hJ hbJ with rfl | rfl
    · exact (hcolJ a haJ).1
    · exact (hcolJ a haJ).2
  · exact absurd hab (by tauto)

end Two

theorem card_coordSet_add (σ : Fin n → Bool) :
    (coordSet σ true).card + (coordSet σ false).card = n := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun i : Fin n => σ i = true)
  rw [Finset.card_univ, Fintype.card_fin] at h
  have e : (Finset.univ.filter fun i : Fin n => ¬ σ i = true) = coordSet σ false := by
    ext i
    simp [coordSet]
  rw [← e]
  exact h

theorem eq_diagonal_of_blocks {B : Matrix (Fin n) (Fin n) k} (σ : Fin n → Bool) (hn : 3 ≤ n)
    (h : ∀ b, 2 ≤ (coordSet σ b).card → ∃ c : k, ∀ a a',
      (a ∈ coordSet σ b ∨ a' ∈ coordSet σ b) → B a a' = if a = a' then c else 0) :
    ∃ u : Fin n → k, (∀ i j, σ i = σ j → u i = u j) ∧ B = diagonal u := by
  have hpair : ∀ b, ∀ i j, σ i = b → σ j = b → i ≠ j → 2 ≤ (coordSet σ b).card := by
    intro b i j hi hj hij
    exact Finset.one_lt_card.mpr ⟨i, mem_coordSet.mpr hi, j, mem_coordSet.mpr hj, hij⟩
  have hsum := card_coordSet_add σ
  refine ⟨fun a => B a a, fun i j hij => ?_, ?_⟩
  · show B i i = B j j
    by_cases hne : i = j
    · rw [hne]
    · obtain ⟨c, hc⟩ := h (σ i) (hpair (σ i) i j rfl hij.symm hne)
      rw [hc i i (Or.inl (mem_coordSet.mpr rfl)), hc j j (Or.inr (mem_coordSet.mpr hij.symm)),
        ite_eq_left rfl, ite_eq_left rfl]
  · ext a a'
    by_cases haa : a = a'
    · rw [haa, diagonal_apply_eq]
    · rw [diagonal_apply_ne _ haa]
      have hbig : 2 ≤ (coordSet σ (σ a)).card ∨ 2 ≤ (coordSet σ (σ a')).card := by
        by_cases hs : σ a = σ a'
        · exact Or.inl (hpair (σ a) a a' rfl hs.symm haa)
        · by_contra hcon
          push Not at hcon
          rcases hσa : σ a <;> rcases hσa' : σ a' <;> rw [hσa, hσa'] at hcon <;>
            simp_all <;> omega
      rcases hbig with hb | hb
      · obtain ⟨c, hc⟩ := h (σ a) hb
        rw [hc a a' (Or.inl (mem_coordSet.mpr rfl)), ite_eq_right haa]
      · obtain ⟨c, hc⟩ := h (σ a') hb
        rw [hc a a' (Or.inr (mem_coordSet.mpr rfl)), ite_eq_right haa]

end CFSG.ComponentClassification.Foote5.OddLieCore
