module

public import CFSG.ClassicalInvolution.RouteD.PatternA

public section

namespace CFSG.ClassicalInvolution.RouteD

open TauCeti

variable {n : ℕ}

theorem B_eq_tri (i j : Fin n) : CartanMatrix.B n i j =
    if i = j then 2 else if i.val + 1 = j.val then -(if j.val + 1 = n then 2 else 1) else
      if j.val + 1 = i.val then -1 else 0 := by
  unfold CartanMatrix.B
  simp only [Matrix.of_apply]
  have hi := i.isLt
  have hj := j.isLt
  by_cases hij : i = j
  · subst hij; simp
  · have h' : i.val ≠ j.val := fun e => hij (Fin.ext e)
    simp only [hij, ite_false]
    split_ifs <;> omega

theorem C_mod2 (i j : Fin n) : ((CartanMatrix.B n i j : ℤ) : ZMod 2) =
    if (i.val + 1 = j.val ∧ j.val + 1 ≠ n) ∨ j.val + 1 = i.val then 1 else 0 := by
  rw [B_eq_tri]
  by_cases h : i = j
  · subst h
    have hc : ¬ (((i : ℕ) + 1 = i ∧ (i : ℕ) + 1 ≠ n) ∨ (i : ℕ) + 1 = i) := by omega
    simp only [hc, ↓reduceIte]
    simp
    decide
  · have h' : i.val ≠ j.val := fun e => h (Fin.ext e)
    by_cases hc : ((i : ℕ) + 1 = j ∧ (j : ℕ) + 1 ≠ n) ∨ (j : ℕ) + 1 = i
    · simp only [hc, ↓reduceIte]
      simp only [h, ↓reduceIte]
      by_cases h1 : (i : ℕ) + 1 = j
      · have h2 : ¬ ((j : ℕ) + 1 = n) := by omega
        simp only [h1, h2, ↓reduceIte]
        decide
      · have h2 : (j : ℕ) + 1 = i := by omega
        simp only [h1, h2, ↓reduceIte]
        decide
    · simp only [hc, ↓reduceIte]
      simp only [h, ↓reduceIte]
      by_cases h1 : (i : ℕ) + 1 = j
      · have h2 : (j : ℕ) + 1 = n := by omega
        simp only [h1, h2, ↓reduceIte]
        decide
      · have h2 : ¬ ((j : ℕ) + 1 = i) := by omega
        simp only [h1, h2, ↓reduceIte]
        decide

@[expose] def picC (n : ℕ) (t : ℕ → ZMod 2) (c : ZMod 2) : Fin n → ZMod 2 :=
  fun j => if j.val + 1 < n then t j + t (j + 1) else c

@[expose] def addAt (t : ℕ → ZMod 2) (k : ℕ) (c : ZMod 2) : ℕ → ZMod 2 :=
  fun m => if m = k then t m + c else t m

theorem charRefl_picC_swap (i : ℕ) (hi : i + 1 < n) (t : ℕ → ZMod 2) (c : ZMod 2) :
    charRefl (CartanMatrix.B n) ⟨i, by omega⟩ (picC n t c) = picC n (swapAt t i) c := by
  funext j
  simp only [charRefl, picC, C_mod2, hi, ↓reduceIte]
  have hj := j.isLt
  by_cases hji : (j : ℕ) = i
  · have cc : (if (i + 1 = (j : ℕ) ∧ (j : ℕ) + 1 ≠ n) ∨ (j : ℕ) + 1 = i then (1 : ZMod 2) else 0) = 0 := by
      have : ¬ ((i + 1 = (j : ℕ) ∧ (j : ℕ) + 1 ≠ n) ∨ (j : ℕ) + 1 = i) := by omega
      simp only [this, ↓reduceIte]
    have hjn : (j : ℕ) + 1 < n := by omega
    rw [cc, zero_mul, add_zero]
    simp only [hji, hi, ↓reduceIte, swapAt_left, swapAt_right]
    exact add_comm _ _
  · by_cases hj1 : (j : ℕ) + 1 = i
    · have cc : (if (i + 1 = (j : ℕ) ∧ (j : ℕ) + 1 ≠ n) ∨ (j : ℕ) + 1 = i then (1 : ZMod 2) else 0) = 1 := by
        have : ((i + 1 = (j : ℕ) ∧ (j : ℕ) + 1 ≠ n) ∨ (j : ℕ) + 1 = i) := Or.inr hj1
        simp only [this, ↓reduceIte]
      have hjn : (j : ℕ) + 1 < n := by omega
      have key : ∀ x y z : ZMod 2, x + y + (y + z) = x + z := by decide
      rw [cc, one_mul]
      simp only [hjn, ↓reduceIte]
      rw [swapAt_of_ne hji (by omega), hj1, swapAt_left]
      exact key _ _ _
    · by_cases hi1 : i + 1 = (j : ℕ)
      · by_cases hjn : (j : ℕ) + 1 < n
        · have cc : (if (i + 1 = (j : ℕ) ∧ (j : ℕ) + 1 ≠ n) ∨ (j : ℕ) + 1 = i then (1 : ZMod 2) else 0) = 1 := by
            have : ((i + 1 = (j : ℕ) ∧ (j : ℕ) + 1 ≠ n) ∨ (j : ℕ) + 1 = i) := Or.inl ⟨hi1, by omega⟩
            simp only [this, ↓reduceIte]
          have key : ∀ x y z : ZMod 2, y + z + (x + y) = x + z := by decide
          rw [cc, one_mul]
          simp only [hjn, ↓reduceIte]
          rw [← hi1, swapAt_right, swapAt_of_ne (by omega) (by omega)]
          exact key _ _ _
        · have cc : (if (i + 1 = (j : ℕ) ∧ (j : ℕ) + 1 ≠ n) ∨ (j : ℕ) + 1 = i then (1 : ZMod 2) else 0) = 0 := by
            have : ¬ ((i + 1 = (j : ℕ) ∧ (j : ℕ) + 1 ≠ n) ∨ (j : ℕ) + 1 = i) := by omega
            simp only [this, ↓reduceIte]
          rw [cc, zero_mul, add_zero]
          simp only [hjn, ↓reduceIte]
      · have cc : (if (i + 1 = (j : ℕ) ∧ (j : ℕ) + 1 ≠ n) ∨ (j : ℕ) + 1 = i then (1 : ZMod 2) else 0) = 0 := by
          have : ¬ ((i + 1 = (j : ℕ) ∧ (j : ℕ) + 1 ≠ n) ∨ (j : ℕ) + 1 = i) := by omega
          simp only [this, ↓reduceIte]
        rw [cc, zero_mul, add_zero]
        by_cases hjn : (j : ℕ) + 1 < n
        · simp only [hjn, ↓reduceIte]
          rw [swapAt_of_ne hji (by omega),
            swapAt_of_ne (show (j : ℕ) + 1 ≠ i by omega) (show (j : ℕ) + 1 ≠ i + 1 by omega)]
        · simp only [hjn, ↓reduceIte]

theorem charRefl_picC_flip (hn : 1 ≤ n) (t : ℕ → ZMod 2) (c : ZMod 2) :
    charRefl (CartanMatrix.B n) ⟨n - 1, by omega⟩ (picC n t c) = picC n (addAt t (n - 1) c) c := by
  funext j
  simp only [charRefl, picC, C_mod2, show ¬ (n - 1 + 1 < n) by omega, ↓reduceIte]
  have hj := j.isLt
  by_cases hjn : (j : ℕ) + 1 < n
  · simp only [hjn, ↓reduceIte, addAt]
    by_cases h1 : (j : ℕ) + 1 = n - 1
    · have cc : (if (n - 1 + 1 = (j : ℕ) ∧ (j : ℕ) + 1 ≠ n) ∨ (j : ℕ) + 1 = n - 1 then (1 : ZMod 2) else 0) = 1 := by
        have : ((n - 1 + 1 = (j : ℕ) ∧ (j : ℕ) + 1 ≠ n) ∨ (j : ℕ) + 1 = n - 1) := Or.inr h1
        simp only [this, ↓reduceIte]
      rw [cc, one_mul]
      simp only [h1, ↓reduceIte, show (j : ℕ) ≠ n - 1 by omega]
      have key : ∀ x y c : ZMod 2, x + y + c = x + (y + c) := by decide
      exact key _ _ _
    · have cc : (if (n - 1 + 1 = (j : ℕ) ∧ (j : ℕ) + 1 ≠ n) ∨ (j : ℕ) + 1 = n - 1 then (1 : ZMod 2) else 0) = 0 := by
        have : ¬ ((n - 1 + 1 = (j : ℕ) ∧ (j : ℕ) + 1 ≠ n) ∨ (j : ℕ) + 1 = n - 1) := by omega
        simp only [this, ↓reduceIte]
      rw [cc, zero_mul, add_zero]
      simp only [h1, ↓reduceIte, show (j : ℕ) ≠ n - 1 by omega]
  · have hjn1 : (j : ℕ) = n - 1 := by omega
    have cc : (if (n - 1 + 1 = (j : ℕ) ∧ (j : ℕ) + 1 ≠ n) ∨ (j : ℕ) + 1 = n - 1 then (1 : ZMod 2) else 0) = 0 := by
      have : ¬ ((n - 1 + 1 = (j : ℕ) ∧ (j : ℕ) + 1 ≠ n) ∨ (j : ℕ) + 1 = n - 1) := by omega
      simp only [this, ↓reduceIte]
    rw [cc, zero_mul, add_zero]
    simp only [hjn, ↓reduceIte]

theorem swap_add_swap (t : ℕ → ZMod 2) (k : ℕ) (c : ZMod 2) :
    swapAt (addAt (swapAt t k) (k + 1) c) k = addAt t k c := by
  funext m
  by_cases h1 : m = k
  · subst h1
    simp [swapAt, addAt]
  · by_cases h2 : m = k + 1
    · subst h2
      simp [swapAt, addAt]
    · simp [swapAt, addAt, h1, h2]

theorem reach_flip_C : ∀ (d k : ℕ), k + 1 + d = n → ∀ t : ℕ → ZMod 2,
    CharReach (CartanMatrix.B n) (picC n t 1) (picC n (addAt t k 1) 1) := by
  intro d
  induction d with
  | zero =>
    intro k hk t
    have : k = n - 1 := by omega
    subst this
    have h := charRefl_picC_flip (n := n) (by omega) t 1
    rw [← h]
    exact CharReach.single' _ _
  | succ d ih =>
    intro k hk t
    have hkn : k + 1 < n := by omega
    have s1 := charRefl_picC_swap k hkn t 1
    have s2 := charRefl_picC_swap k hkn (addAt (swapAt t k) (k + 1) 1) 1
    rw [swap_add_swap] at s2
    have step1 : CharReach (CartanMatrix.B n) (picC n t 1) (picC n (swapAt t k) 1) := by
      rw [← s1]; exact CharReach.single' _ _
    have step2 : CharReach (CartanMatrix.B n) (picC n (addAt (swapAt t k) (k + 1) 1) 1)
        (picC n (addAt t k 1) 1) := by
      rw [← s2]; exact CharReach.single' _ _
    exact (step1.trans' (ih (k + 1) (by omega) _)).trans' step2

@[expose] def zeroFirst (t : ℕ → ZMod 2) (m : ℕ) : ℕ → ZMod 2 := fun k => if k < m then 0 else t k

theorem reach_zero_C (t : ℕ → ZMod 2) : ∀ m, m ≤ n →
    CharReach (CartanMatrix.B n) (picC n t 1) (picC n (zeroFirst t m) 1) := by
  intro m
  induction m with
  | zero =>
    intro _
    have : zeroFirst t 0 = t := by funext k; simp [zeroFirst]
    rw [this]; exact CharReach.refl' _ _
  | succ m ih =>
    intro hm
    have h0 := ih (by omega)
    by_cases htm : t m = 1
    · have hflip := reach_flip_C (n := n) (n - m - 1) m (by omega) (zeroFirst t m)
      have : addAt (zeroFirst t m) m 1 = zeroFirst t (m + 1) := by
        funext k
        by_cases h1 : k = m
        · subst h1; simp [addAt, zeroFirst, htm]; decide
        · by_cases h2 : k < m
          · simp [addAt, zeroFirst, h1, h2, show k < m + 1 by omega]
          · simp [addAt, zeroFirst, h1, h2, show ¬ k < m + 1 by omega]
      rw [this] at hflip
      exact h0.trans' hflip
    · have : zeroFirst t (m + 1) = zeroFirst t m := by
        have h0' : t m = 0 := by revert htm; generalize t m = x; revert x; decide
        funext k
        by_cases h1 : k = m
        · subst h1; simp [zeroFirst, h0']
        · by_cases h2 : k < m
          · simp [zeroFirst, h2, show k < m + 1 by omega]
          · simp [zeroFirst, h2, show ¬ k < m + 1 by omega]
      rw [this]; exact h0

theorem patternLemma_C (n : ℕ) : PatternLemma (CartanMatrix.B n) := by
  intro v hv
  obtain ⟨j0, hj0⟩ : ∃ j, v j ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  have hn : 1 ≤ n := by have := j0.isLt; omega
  set t := prefixSum v with ht
  set c : ZMod 2 := v ⟨n - 1, by omega⟩ with hc
  have hpic : picC n t c = v := by
    funext j
    have h := congrFun (picA_prefixSum v) j
    simp only [picC]
    by_cases hj : (j : ℕ) + 1 < n
    · simp only [hj, ↓reduceIte]
      exact h
    · have : j = ⟨n - 1, by omega⟩ := Fin.ext (by have := j.isLt; simp; omega)
      simp only [hj, ↓reduceIte]
      rw [hc, this]
  have key : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases key c with hc0 | hc1
  ·
    have hj0n : (j0 : ℕ) + 1 < n := by
      by_contra h
      have : j0 = ⟨n - 1, by omega⟩ := Fin.ext (by have := j0.isLt; simp; omega)
      apply hj0
      rw [this]
      exact hc0
    have hmix : (∃ k, k < n ∧ t k = 0) ∧ (∃ k, k < n ∧ t k = 1) := by
      have h1 : t j0 + t (j0 + 1) = v j0 := by
        rw [← hpic]; simp [picC, hj0n]
      have key2 : ∀ x y : ZMod 2, x + y ≠ 0 → (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) := by decide
      rcases key2 _ _ (by rw [h1]; exact hj0) with ⟨h2, h3⟩ | ⟨h2, h3⟩
      · exact ⟨⟨j0, by omega, h2⟩, ⟨j0 + 1, by omega, h3⟩⟩
      · exact ⟨⟨j0 + 1, by omega, h3⟩, ⟨j0, by omega, h2⟩⟩
    obtain ⟨t', a, hr, ha, hs, hfix⟩ := sort_swaps 0 n t
    have hreach := lift_swaps (A := CartanMatrix.B n) (fun t => picC n t c) n
      (fun i hi => ⟨i, by omega⟩) (fun i hi t => charRefl_picC_swap i hi t c) hr
    rw [hpic] at hreach
    have hm0 := reflTransGen_Sw_val_pres hr 0 hmix.1
    have hm1 := reflTransGen_Sw_val_pres hr 1 hmix.2
    obtain ⟨ha0, ha1⟩ := sorted_cut (u := 0) hs (by simpa using hm0) (by simpa using hm1)
    refine ⟨picC n t' c, hreach, ⟨a - 1, by omega⟩, ?_⟩
    funext j
    have hjn := j.isLt
    simp only [picC, Pi.single_apply, Fin.ext_iff, hc0]
    by_cases hj1 : (j : ℕ) + 1 < n
    · rw [hs j (by omega), hs (j + 1) hj1]
      simp only [hj1, ↓reduceIte]
      by_cases h1 : (j : ℕ) < a
      · by_cases h2 : (j : ℕ) + 1 < a
        · have h3 : ¬ ((j : ℕ) = a - 1) := by omega
          simp only [h1, h2, h3, ↓reduceIte, add_zero]
        · have h3 : (j : ℕ) = a - 1 := by omega
          simp only [h1, h2, ↓reduceIte]
          simp only [h3, ↓reduceIte]
          decide
      · have h2 : ¬ ((j : ℕ) + 1 < a) := by omega
        have h3 : ¬ ((j : ℕ) = a - 1) := by omega
        simp only [h1, h2, h3, ↓reduceIte]
        decide
    · have h3 : ¬ ((j : ℕ) = a - 1) := by omega
      simp only [hj1, h3, ↓reduceIte]
  ·
    have hz := reach_zero_C (n := n) t n le_rfl
    rw [hc1] at hpic
    refine ⟨picC n (zeroFirst t n) 1, ?_, ⟨n - 1, by omega⟩, ?_⟩
    · rw [← hpic]; exact hz
    · funext j
      have hjn := j.isLt
      simp only [picC, Pi.single_apply, Fin.ext_iff]
      by_cases hj1 : (j : ℕ) + 1 < n
      · simp only [hj1, ↓reduceIte, zeroFirst, show (j : ℕ) < n by omega,
          show (j : ℕ) ≠ n - 1 by omega, add_zero]
      · simp only [hj1, ↓reduceIte]
        simp only [show (j : ℕ) = n - 1 by omega, ↓reduceIte]

end CFSG.ClassicalInvolution.RouteD
