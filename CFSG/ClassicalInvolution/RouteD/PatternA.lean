module

public import CFSG.ClassicalInvolution.RouteD.PatternBasic

public section

namespace CFSG.ClassicalInvolution.RouteD

open TauCeti

variable {n : ℕ}

theorem A_mod2 (i j : Fin n) : ((CartanMatrix.A n i j : ℤ) : ZMod 2) =
    if i.val + 1 = j.val ∨ j.val + 1 = i.val then 1 else 0 := by
  unfold CartanMatrix.A
  simp only [Matrix.of_apply]
  by_cases h : i = j
  · subst h
    simp
    decide
  · have h' : i.val ≠ j.val := fun e => h (Fin.ext e)
    by_cases hc : i.val + 1 = j.val ∨ j.val + 1 = i.val <;> simp [h, hc]

@[expose] def picA (n : ℕ) (t : ℕ → ZMod 2) : Fin n → ZMod 2 := fun j => t j + t (j + 1)

theorem charRefl_picA (i : Fin n) (t : ℕ → ZMod 2) :
    charRefl (CartanMatrix.A n) i (picA n t) = picA n (swapAt t i) := by
  funext j
  simp only [charRefl, picA, A_mod2]
  by_cases hji : (j : ℕ) = i
  · have : j = i := Fin.ext hji
    subst this
    simp [swapAt_left, swapAt_right, add_comm]
  · by_cases hj1 : (j : ℕ) + 1 = i
    · have key : ∀ x y z : ZMod 2, x + y + (y + z) = x + z := by decide
      have e1 : swapAt t i j = t j := swapAt_of_ne hji (by omega)
      have e2 : swapAt t i (j + 1) = t (i + 1) := by rw [hj1, swapAt_left]
      have c : (if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then (1 : ZMod 2) else 0) = 1 := by
        simp [hj1]
      rw [c, e1, e2, one_mul, hj1]
      exact key _ _ _
    · by_cases hi1 : (i : ℕ) + 1 = j
      · have key : ∀ x y z : ZMod 2, y + z + (x + y) = x + z := by decide
        have e1 : swapAt t i j = t i := by rw [← hi1, swapAt_right]
        have e2 : swapAt t i (j + 1) = t (i + 1 + 1) :=
          by rw [← hi1]; exact swapAt_of_ne (by omega) (by omega)
        have c : (if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then (1 : ZMod 2) else 0) = 1 := by
          simp [hi1]
        rw [c, e1, e2, one_mul, ← hi1]
        exact key _ _ _
      · have c : (if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then (1 : ZMod 2) else 0) = 0 := by
          have : ¬ ((i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) := by omega
          simp [this]
        rw [c, zero_mul, add_zero, swapAt_of_ne hji (by omega), swapAt_of_ne (by omega) (by omega)]

@[expose] def prefixSum (v : Fin n → ZMod 2) : ℕ → ZMod 2
  | 0 => 0
  | k + 1 => prefixSum v k + (if h : k < n then v ⟨k, h⟩ else 0)

theorem picA_prefixSum (v : Fin n → ZMod 2) : picA n (prefixSum v) = v := by
  funext j
  have key : ∀ x y : ZMod 2, x + (x + y) = y := by decide
  simp only [picA, prefixSum, j.isLt, dite_true]
  exact key _ _

theorem patternLemma_A (n : ℕ) : PatternLemma (CartanMatrix.A n) := by
  intro v hv
  set t := prefixSum v with ht
  have hpic : picA n t = v := picA_prefixSum v
  have hmix : (∃ k, k < n + 1 ∧ t k = 0) ∧ (∃ k, k < n + 1 ∧ t k = 1) := by
    obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
      by_contra h
      push Not at h
      exact hv (funext h)
    have h1 : t j + t (j + 1) = v j := by rw [← hpic]; rfl
    have key : ∀ x y : ZMod 2, x + y ≠ 0 → (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) := by decide
    rcases key _ _ (by rw [h1]; exact hj) with ⟨h2, h3⟩ | ⟨h2, h3⟩
    · exact ⟨⟨j, by omega, h2⟩, ⟨j + 1, by omega, h3⟩⟩
    · exact ⟨⟨j + 1, by omega, h3⟩, ⟨j, by omega, h2⟩⟩
  obtain ⟨t', a, hr, ha, hs, hfix⟩ := sort_swaps 0 (n + 1) t
  have hreach := lift_swaps (A := CartanMatrix.A n) (picA n) (n + 1)
    (fun i hi => ⟨i, by omega⟩) (fun i hi t => charRefl_picA ⟨i, by omega⟩ t) hr
  rw [hpic] at hreach
  have hm0 := reflTransGen_Sw_val_pres hr 0 hmix.1
  have hm1 := reflTransGen_Sw_val_pres hr 1 hmix.2
  obtain ⟨ha0, ha1⟩ := sorted_cut (u := 0) hs (by simpa using hm0) (by simpa using hm1)
  refine ⟨picA n t', hreach, ⟨a - 1, by omega⟩, ?_⟩
  funext j
  have hj := j.isLt
  simp only [picA, Pi.single_apply, Fin.ext_iff]
  rw [hs j (by omega), hs (j + 1) (by omega)]
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

end CFSG.ClassicalInvolution.RouteD
