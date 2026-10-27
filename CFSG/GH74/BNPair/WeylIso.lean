module

public import CFSG.GH74.BNPair.Dihedral

public section

namespace CFSG.GH74.BNPair

variable {W : Type*} [Group W] {x y : W} {n : ℕ}

theorem mul_altWord_x (hx : x * x = 1) (hbraid : altWord x y n = altWord y x n) (hn : 1 ≤ n)
    {t : ℕ} (ht : t ≤ n) :
    x * altWord x y t =
      if Even t then (if t = n then altWord y x (t - 1) else altWord x y (t + 1))
      else altWord x y (t - 1) := by
  have hn1 : n - 1 + 1 = n := by omega
  have hlast := altWord_succ_left y x (n - 1)
  rw [hn1] at hlast
  by_cases hev : Even t
  · by_cases htn : t = n
    · subst htn
      have hodd : ¬ Even (t - 1) := by
        intro h'
        obtain ⟨k, hk⟩ := hev
        obtain ⟨l, hl⟩ := h'
        omega
      rw [ite_eq_left hev, ite_eq_left rfl, hbraid, hlast]
      simp [hodd, ← mul_assoc, hx]
    · rw [ite_eq_left hev, ite_eq_right htn]
      exact mul_altWord_even t hev
  · rw [ite_eq_right hev]
    exact mul_altWord_odd' hx t hev

theorem mul_altWord_y (hy : y * y = 1) (hbraid : altWord x y n = altWord y x n) (hn : 1 ≤ n)
    {t : ℕ} (ht : t ≤ n) :
    y * altWord x y t =
      if Even t then (if t = 0 then altWord y x 1 else altWord x y (t - 1))
      else (if t = n then altWord y x (t - 1) else altWord x y (t + 1)) := by
  have hn1 : n - 1 + 1 = n := by omega
  have hlast := altWord_succ_left y x (n - 1)
  rw [hn1] at hlast
  by_cases hev : Even t
  · rw [ite_eq_left hev]
    by_cases ht0 : t = 0
    · subst ht0
      rw [ite_eq_left rfl]
      simp [altWord_zero, altWord_one]
    · rw [ite_eq_right ht0]
      exact mul_altWord_even' hy t hev ht0
  · rw [ite_eq_right hev]
    by_cases htn : t = n
    · subst htn
      have heven : Even (t - 1) := by
        have : ¬ Even t := hev
        rw [Nat.even_sub (by omega)]
        simpa using this
      rw [ite_eq_left rfl, hbraid, hlast]
      simp [heven, ← mul_assoc, hy]
    · rw [ite_eq_right htn]
      exact mul_altWord_odd t hev

@[expose] def altParam' (a b : W) (n : ℕ) : Fin (n + 1) ⊕ Fin (n - 1) → W
  | Sum.inl i => altWord a b i
  | Sum.inr j => altWord b a (j + 1)

theorem IsDihedralGen.altParam'_bijective (h : IsDihedralGen x y n) :
    Function.Bijective (altParam' x y n) := by
  have hfin : Finite W := Nat.finite_of_card_ne_zero (by rw [h.card_eq]; have := h.three_le; omega)
  have hsurj : Function.Surjective (altParam' x y n) := by
    intro w
    obtain ⟨t, htn, ht | ht⟩ := h.exists_altWord w
    · exact ⟨Sum.inl ⟨t, by omega⟩, ht.symm⟩
    · by_cases ht0 : t = 0
      · subst ht0
        exact ⟨Sum.inl 0, by simpa [altParam', altWord_zero] using ht.symm⟩
      by_cases htn' : t = n
      · subst htn'
        exact ⟨Sum.inl ⟨t, by omega⟩, by simpa [altParam'] using (ht.trans h.altWord_eq.symm).symm⟩
      · exact ⟨Sum.inr ⟨t - 1, by omega⟩, by
          simp only [altParam']
          rw [show t - 1 + 1 = t by omega]
          exact ht.symm⟩
  refine hsurj.bijective_of_nat_card_le ?_
  rw [Nat.card_sum, h.card_eq]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  have := h.three_le
  omega

section Iso

variable {W' : Type*} [Group W'] {x' y' : W'}

theorem IsDihedralGen.exists_weylIso (h : IsDihedralGen x y n) (h' : IsDihedralGen x' y' n) :
    ∃ ι : W ≃ W', (∀ t ≤ n, ι (altWord x y t) = altWord x' y' t) ∧
      (∀ t ≤ n, ι (altWord y x t) = altWord y' x' t) ∧
      (∀ w, ι (x * w) = x' * ι w) ∧ (∀ w, ι (y * w) = y' * ι w) := by
  have hn := h.three_le
  let e := Equiv.ofBijective _ h.altParam'_bijective
  let e' := Equiv.ofBijective _ h'.altParam'_bijective
  let ι : W ≃ W' := e.symm.trans e'
  have hA : ∀ t ≤ n, ι (altWord x y t) = altWord x' y' t := by
    intro t ht
    have : altWord x y t = e (Sum.inl ⟨t, by omega⟩) := rfl
    simp [ι, this, e', altParam']
  have hB : ∀ t ≤ n, ι (altWord y x t) = altWord y' x' t := by
    intro t ht
    by_cases ht0 : t = 0
    · subst ht0
      rw [altWord_zero, altWord_zero]
      have := hA 0 (by omega)
      rwa [altWord_zero, altWord_zero] at this
    by_cases htn : t = n
    · subst htn
      rw [← h.altWord_eq, ← h'.altWord_eq]
      exact hA _ le_rfl
    · have : altWord y x t = e (Sum.inr ⟨t - 1, by omega⟩) := by
        simp only [e, Equiv.ofBijective_apply, altParam']
        rw [show t - 1 + 1 = t by omega]
      simp only [ι, this, Equiv.trans_apply, Equiv.symm_apply_apply, e', Equiv.ofBijective_apply,
        altParam']
      rw [show t - 1 + 1 = t by omega]
  have hx := h.mul_self_a
  have hy := h.mul_self_b
  have hx' := h'.mul_self_a
  have hy' := h'.mul_self_b
  have hbr := h.altWord_eq
  have hbr' := h'.altWord_eq
  have hbr2 : altWord y x n = altWord x y n := hbr.symm
  have hbr2' : altWord y' x' n = altWord x' y' n := hbr'.symm
  refine ⟨ι, hA, hB, ?_, ?_⟩
  · intro w
    obtain ⟨t, ht, rfl | rfl⟩ := h.exists_altWord w
    · rw [mul_altWord_x hx hbr (by omega) ht, hA t ht, mul_altWord_x hx' hbr' (by omega) ht]
      split_ifs <;> first | exact hA _ (by omega) | exact hB _ (by omega)
    · rw [mul_altWord_y hx hbr2 (by omega) ht, hB t ht, mul_altWord_y hx' hbr2' (by omega) ht]
      split_ifs <;> first | exact hA _ (by omega) | exact hB _ (by omega)
  · intro w
    obtain ⟨t, ht, rfl | rfl⟩ := h.exists_altWord w
    · rw [mul_altWord_y hy hbr (by omega) ht, hA t ht, mul_altWord_y hy' hbr' (by omega) ht]
      split_ifs <;> first | exact hA _ (by omega) | exact hB _ (by omega)
    · rw [mul_altWord_x hy hbr2 (by omega) ht, hB t ht, mul_altWord_x hy' hbr2' (by omega) ht]
      split_ifs <;> first | exact hA _ (by omega) | exact hB _ (by omega)

end Iso

theorem IsDihedralGen.ell_gen_mul (h : IsDihedralGen x y n) {s : W} (hs : s = x ∨ s = y) (w : W) :
    wordLength ({x, y} : Set W) (s * w) + 1 = wordLength ({x, y} : Set W) w ∨
      wordLength ({x, y} : Set W) w + 1 = wordLength ({x, y} : Set W) (s * w) := by
  have hn := h.three_le
  have hx := h.mul_self_a
  have hy := h.mul_self_b
  have hbr := h.altWord_eq
  have hbr2 : altWord y x n = altWord x y n := hbr.symm
  have hL : ∀ {j : ℕ}, j ≤ n → wordLength ({x, y} : Set W) (altWord x y j) = j :=
    fun hj => h.wordLength_altWord hj
  have hL' : ∀ {j : ℕ}, j ≤ n → wordLength ({x, y} : Set W) (altWord y x j) = j :=
    fun hj => h.wordLength_altWord' hj
  have hodd : ∀ t : ℕ, ¬ Even t → 1 ≤ t := fun t hne => by
    by_contra h0
    exact hne (by obtain rfl : t = 0 := by omega
                  exact ⟨0, rfl⟩)
  obtain ⟨t, ht, rfl | rfl⟩ := h.exists_altWord w
  · rcases hs with rfl | rfl
    · rw [mul_altWord_x hx hbr (by omega) ht, hL ht]
      split_ifs <;> simp (disch := omega) only [hL, hL', or_true] <;>
        first | omega | (have := hodd t ‹_›; omega)
    · rw [mul_altWord_y hy hbr (by omega) ht, hL ht]
      split_ifs <;> simp (disch := omega) only [hL, hL', or_true] <;> omega
  · rcases hs with rfl | rfl
    · rw [mul_altWord_y hx hbr2 (by omega) ht, hL' ht]
      split_ifs <;> simp (disch := omega) only [hL, hL', or_true] <;> omega
    · rw [mul_altWord_x hy hbr2 (by omega) ht, hL' ht]
      split_ifs <;> simp (disch := omega) only [hL, hL', or_true] <;>
        first | omega | (have := hodd t ‹_›; omega)

theorem IsDihedralGen.eq_altWord_of_wordLength_eq (h : IsDihedralGen x y n) {w : W}
    (hw : wordLength ({x, y} : Set W) w = n) : w = altWord x y n := by
  obtain ⟨t, ht, rfl | rfl⟩ := h.exists_altWord w
  · rw [h.wordLength_altWord ht] at hw
    rw [hw]
  · rw [h.wordLength_altWord' ht] at hw
    rw [hw]
    exact h.altWord_eq.symm

theorem IsDihedralGen.eq_one_of_wordLength_eq_zero (h : IsDihedralGen x y n) {w : W}
    (hw : wordLength ({x, y} : Set W) w = 0) : w = 1 := by
  have hJ : ∀ s ∈ ({x, y} : Set W), s * s = 1 := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact h.mul_self_a
    · exact h.mul_self_b
  have hw' : w ∈ Subgroup.closure ({x, y} : Set W) := by rw [h.closure_eq]; trivial
  exact (wordLength_eq_zero_iff hJ hw').1 hw

theorem IsDihedralGen.wordLength_gen (h : IsDihedralGen x y n) {s : W} (hs : s = x ∨ s = y) :
    wordLength ({x, y} : Set W) s = 1 := by
  have := h.ell_gen_mul hs 1
  rw [mul_one, wordLength_one] at this
  omega

theorem IsDihedralGen.exactly_one_ascent (h : IsDihedralGen x y n) {w : W}
    (h0 : 0 < wordLength ({x, y} : Set W) w) (hn : wordLength ({x, y} : Set W) w < n) :
    (wordLength ({x, y} : Set W) (x * w) < wordLength ({x, y} : Set W) w ∧
        wordLength ({x, y} : Set W) w < wordLength ({x, y} : Set W) (y * w)) ∨
      (wordLength ({x, y} : Set W) (y * w) < wordLength ({x, y} : Set W) w ∧
        wordLength ({x, y} : Set W) w < wordLength ({x, y} : Set W) (x * w)) := by
  have hn3 := h.three_le
  have hx := h.mul_self_a
  have hy := h.mul_self_b
  have hbr := h.altWord_eq
  have hbr2 : altWord y x n = altWord x y n := hbr.symm
  have hL : ∀ {j : ℕ}, j ≤ n → wordLength ({x, y} : Set W) (altWord x y j) = j :=
    fun hj => h.wordLength_altWord hj
  have hL' : ∀ {j : ℕ}, j ≤ n → wordLength ({x, y} : Set W) (altWord y x j) = j :=
    fun hj => h.wordLength_altWord' hj
  obtain ⟨t, ht, rfl | rfl⟩ := h.exists_altWord w
  · rw [hL ht] at h0 hn ⊢
    rw [mul_altWord_x hx hbr (by omega) ht, mul_altWord_y hy hbr (by omega) ht]
    split_ifs <;> simp (disch := omega) only [hL, hL'] <;> omega
  · rw [hL' ht] at h0 hn ⊢
    rw [mul_altWord_x hy hbr2 (by omega) ht, mul_altWord_y hx hbr2 (by omega) ht]
    split_ifs <;> simp (disch := omega) only [hL, hL'] <;> omega

end CFSG.GH74.BNPair
