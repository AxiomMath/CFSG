module

public import CFSG.ClassicalInvolution.RouteD.PatternBasic

public section

namespace CFSG.ClassicalInvolution.RouteD

open TauCeti

variable {n : ℕ}

theorem C_eq_tri (i j : Fin n) : CartanMatrix.C n i j =
    if i = j then 2 else if j.val + 1 = i.val then -(if i.val + 1 = n then 2 else 1) else
      if i.val + 1 = j.val then -1 else 0 := by
  unfold CartanMatrix.C
  simp only [Matrix.of_apply]
  have hi := i.isLt
  have hj := j.isLt
  by_cases hij : i = j
  · subst hij; simp
  · have h' : i.val ≠ j.val := fun e => hij (Fin.ext e)
    simp only [hij, ite_false]
    split_ifs <;> omega

theorem B_mod2 (i j : Fin n) : ((CartanMatrix.C n i j : ℤ) : ZMod 2) =
    if i.val + 1 = j.val ∨ (j.val + 1 = i.val ∧ i.val + 1 ≠ n) then 1 else 0 := by
  rw [C_eq_tri]
  by_cases h : i = j
  · subst h
    have hc : ¬ ((i : ℕ) + 1 = i ∨ ((i : ℕ) + 1 = i ∧ (i : ℕ) + 1 ≠ n)) := by omega
    simp only [hc, ↓reduceIte]
    simp
    decide
  · have h' : i.val ≠ j.val := fun e => h (Fin.ext e)
    by_cases hc : (i : ℕ) + 1 = j ∨ ((j : ℕ) + 1 = i ∧ (i : ℕ) + 1 ≠ n)
    · simp only [hc, ↓reduceIte]
      simp only [h, ↓reduceIte]
      by_cases h1 : j.val + 1 = i.val
      · have h2 : ¬ ((i : ℕ) + 1 = n) := by omega
        have h3 : ¬ ((i : ℕ) + 1 = j) := by omega
        simp only [h1, h2, ↓reduceIte]
        decide
      · have h2 : (i : ℕ) + 1 = j := by omega
        simp only [h1, h2, ↓reduceIte]
        decide
    · simp only [hc, ↓reduceIte]
      simp only [h, ↓reduceIte]
      have h1 : ¬ ((j : ℕ) + 1 = i ∧ (i : ℕ) + 1 ≠ n) := by omega
      have h2 : ¬ ((i : ℕ) + 1 = j) := by omega
      by_cases h3 : (j : ℕ) + 1 = i
      · have h4 : (i : ℕ) + 1 = n := by omega
        simp only [h3, h4, ↓reduceIte]
        decide
      · simp only [h3, h2, ↓reduceIte]
        decide

@[expose] def picB (n : ℕ) (t : ℕ → ZMod 2) : Fin n → ZMod 2 :=
  fun j => t j + (if j.val + 1 < n then t (j + 1) else 0)

theorem charRefl_picB (i : ℕ) (hi : i + 1 < n) (t : ℕ → ZMod 2) :
    charRefl (CartanMatrix.C n) ⟨i, by omega⟩ (picB n t) = picB n (swapAt t i) := by
  funext j
  simp only [charRefl, picB, B_mod2, hi, ↓reduceIte]
  have hj := j.isLt
  by_cases hji : (j : ℕ) = i
  · have c : (if i + 1 = (j : ℕ) ∨ ((j : ℕ) + 1 = i ∧ i + 1 ≠ n) then (1 : ZMod 2) else 0) = 0 := by
      have : ¬ (i + 1 = (j : ℕ) ∨ ((j : ℕ) + 1 = i ∧ i + 1 ≠ n)) := by omega
      simp only [this, ↓reduceIte]
    rw [c, zero_mul, add_zero]
    simp only [hji, hi, ↓reduceIte, swapAt_left, swapAt_right]
    exact add_comm _ _
  · by_cases hj1 : (j : ℕ) + 1 = i
    · have c : (if i + 1 = (j : ℕ) ∨ ((j : ℕ) + 1 = i ∧ i + 1 ≠ n) then (1 : ZMod 2) else 0) = 1 := by
        have : (i + 1 = (j : ℕ) ∨ ((j : ℕ) + 1 = i ∧ i + 1 ≠ n)) := Or.inr ⟨hj1, by omega⟩
        simp only [this, ↓reduceIte]
      have hjn : (j : ℕ) + 1 < n := by omega
      have key : ∀ x y z : ZMod 2, x + y + (y + z) = x + z := by decide
      rw [c, one_mul]
      simp only [hjn, ↓reduceIte]
      rw [swapAt_of_ne hji (by omega), hj1, swapAt_left]
      exact key _ _ _
    · by_cases hi1 : i + 1 = (j : ℕ)
      · have c : (if i + 1 = (j : ℕ) ∨ ((j : ℕ) + 1 = i ∧ i + 1 ≠ n) then (1 : ZMod 2) else 0) = 1 := by
          have : (i + 1 = (j : ℕ) ∨ ((j : ℕ) + 1 = i ∧ i + 1 ≠ n)) := Or.inl hi1
          simp only [this, ↓reduceIte]
        rw [c, one_mul]
        by_cases hjn : (j : ℕ) + 1 < n
        · have key : ∀ x y z : ZMod 2, y + z + (x + y) = x + z := by decide
          simp only [hjn, ↓reduceIte]
          rw [← hi1, swapAt_right, swapAt_of_ne (by omega) (by omega)]
          exact key _ _ _
        · have key : ∀ x y : ZMod 2, y + 0 + (x + y) = x + 0 := by decide
          simp only [hjn, ↓reduceIte]
          rw [← hi1, swapAt_right]
          exact key _ _
      · have c : (if i + 1 = (j : ℕ) ∨ ((j : ℕ) + 1 = i ∧ i + 1 ≠ n) then (1 : ZMod 2) else 0) = 0 := by
          have : ¬ (i + 1 = (j : ℕ) ∨ ((j : ℕ) + 1 = i ∧ i + 1 ≠ n)) := by omega
          simp only [this, ↓reduceIte]
        rw [c, zero_mul, add_zero, swapAt_of_ne hji (by omega),
          swapAt_of_ne (show (j : ℕ) + 1 ≠ i by omega) (show (j : ℕ) + 1 ≠ i + 1 by omega)]

@[expose] def suffixSum (v : Fin n → ZMod 2) (k : ℕ) : ZMod 2 :=
  ∑ j : Fin n, if k ≤ j.val then v j else 0

theorem suffixSum_succ (v : Fin n → ZMod 2) (j : Fin n) :
    suffixSum v j.val = v j + suffixSum v (j.val + 1) := by
  unfold suffixSum
  have h : ∀ j' : Fin n, (if j.val ≤ j'.val then v j' else 0) =
      (if j' = j then v j' else 0) + (if j.val + 1 ≤ j'.val then v j' else 0) := by
    intro j'
    by_cases h1 : j' = j
    · subst h1; simp
    · have h2 : j.val ≠ j'.val := fun e => h1 (Fin.ext e.symm)
      by_cases h3 : j.val + 1 ≤ j'.val
      · simp [h1, h3, show j.val ≤ j'.val by omega]
      · simp [h1, h3, show ¬ j.val ≤ j'.val by omega]
  rw [Finset.sum_congr rfl fun j' _ => h j', Finset.sum_add_distrib]
  simp

theorem picB_suffixSum (v : Fin n → ZMod 2) : picB n (suffixSum v) = v := by
  funext j
  have key : ∀ x y : ZMod 2, (x + y) + y = x := by decide
  simp only [picB]
  rw [suffixSum_succ v j]
  by_cases hj : (j : ℕ) + 1 < n
  · simp only [hj, ↓reduceIte]
    exact key _ _
  · have h0 : suffixSum v (j.val + 1) = 0 := by
      unfold suffixSum
      apply Finset.sum_eq_zero
      intro j' _
      have := j'.isLt
      have : ¬ (j.val + 1 ≤ j'.val) := by omega
      simp [this]
    simp only [hj, ↓reduceIte, h0]
    simp

theorem patternLemma_B (n : ℕ) : PatternLemma (CartanMatrix.C n) := by
  intro v hv
  set t := suffixSum v with ht
  have hpic : picB n t = v := picB_suffixSum v
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  have hmix : ∃ k, k < n ∧ t k = 1 := by
    have h1 : t j + (if (j : ℕ) + 1 < n then t (j + 1) else 0) = v j := by rw [← hpic]; rfl
    have key : ∀ x y : ZMod 2, x + y ≠ 0 → x = 1 ∨ y = 1 := by decide
    by_cases hjn : (j : ℕ) + 1 < n
    · simp only [hjn, ↓reduceIte] at h1
      rcases key _ _ (by rw [h1]; exact hj) with h2 | h2
      · exact ⟨j, j.isLt, h2⟩
      · exact ⟨j + 1, hjn, h2⟩
    · simp only [hjn, ↓reduceIte, add_zero] at h1
      exact ⟨j, j.isLt, by rw [h1]; revert hj; generalize v j = x; revert x; decide⟩
  obtain ⟨t', b, hr, hb, hs, hfix⟩ := sort_swaps 1 n t
  have hreach := lift_swaps (A := CartanMatrix.C n) (picB n) n
    (fun i hi => ⟨i, by omega⟩) (fun i hi t => charRefl_picB i hi t) hr
  rw [hpic] at hreach
  obtain ⟨k, hk, hkv⟩ := reflTransGen_Sw_val_pres hr 1 hmix
  rw [hs k hk] at hkv
  have hb1 : 0 < b := by
    by_contra h
    have : ¬ (k < b) := by omega
    simp only [this, ↓reduceIte] at hkv
    revert hkv; decide
  refine ⟨picB n t', hreach, ⟨b - 1, by omega⟩, ?_⟩
  funext j
  have hjn := j.isLt
  simp only [picB, Pi.single_apply, Fin.ext_iff]
  rw [hs j (by omega)]
  by_cases hj1 : (j : ℕ) + 1 < n
  · rw [hs (j + 1) hj1]
    by_cases h1 : (j : ℕ) < b
    · by_cases h2 : (j : ℕ) + 1 < b
      · have h3 : ¬ ((j : ℕ) = b - 1) := by omega
        simp only [hj1, h1, h2, h3, ↓reduceIte]
        decide
      · have h3 : (j : ℕ) = b - 1 := by omega
        simp only [hj1, h1, h2, ↓reduceIte]
        simp only [h3, ↓reduceIte]
        decide
    · have h2 : ¬ ((j : ℕ) + 1 < b) := by omega
      have h3 : ¬ ((j : ℕ) = b - 1) := by omega
      simp only [hj1, h1, h2, h3, ↓reduceIte]
      decide
  · by_cases h1 : (j : ℕ) < b
    · have h3 : (j : ℕ) = b - 1 := by omega
      simp only [hj1, h1, ↓reduceIte]
      simp only [h3, ↓reduceIte]
      decide
    · have h3 : ¬ ((j : ℕ) = b - 1) := by omega
      simp only [hj1, h1, h3, ↓reduceIte]
      decide

end CFSG.ClassicalInvolution.RouteD
