module

public import CFSG.ClassicalInvolution.RouteD.PatternB

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.RouteD TauCeti

variable {n : ℕ}

theorem suffixSum_picB (t : ℕ → ZMod 2) (k : ℕ) (hk : k < n) : suffixSum (picB n t) k = t k := by
  obtain ⟨d, hd⟩ : ∃ d, n - 1 - k = d := ⟨_, rfl⟩
  induction d generalizing k with
  | zero =>
    have hkn : k = n - 1 := by omega
    subst hkn
    have h1 := suffixSum_succ (picB n t) ⟨n - 1, hk⟩
    have h0 : suffixSum (picB n t) (n - 1 + 1) = 0 := by
      unfold suffixSum
      apply Finset.sum_eq_zero
      intro j' _
      have := j'.isLt
      have : ¬ (n - 1 + 1 ≤ j'.val) := by omega
      simp [this]
    have hlt : ¬ (n - 1 + 1 < n) := by omega
    simp only [h0, add_zero, picB, hlt, ↓reduceIte] at h1
    exact h1
  | succ d ih =>
    have hk1 : k + 1 < n := by omega
    have h1 := suffixSum_succ (picB n t) ⟨k, hk⟩
    have h2 := ih (k + 1) hk1 (by omega)
    simp only [picB, hk1, ↓reduceIte] at h1
    rw [h1, h2]
    have key : ∀ x y : ZMod 2, x + y + y = x := by decide
    exact key _ _

@[expose] def onesCount (v : Fin n → ZMod 2) : ℕ :=
  (Finset.univ.filter fun k : Fin n => suffixSum v k.val = 1).card

theorem onesCount_picB (t : ℕ → ZMod 2) :
    onesCount (picB n t) = (Finset.univ.filter fun k : Fin n => t k.val = 1).card := by
  unfold onesCount
  congr 1
  ext k
  simp [suffixSum_picB t k.val k.isLt]

theorem onesCount_charRefl (i : Fin n) (v : Fin n → ZMod 2) :
    onesCount (charRefl (CartanMatrix.C n) i v) = onesCount v := by
  by_cases hi : i.val + 1 < n
  · set t : ℕ → ZMod 2 := suffixSum v with ht
    have hv : v = picB n t := (picB_suffixSum v).symm
    have e : charRefl (CartanMatrix.C n) i v = picB n (swapAt t i.val) := by
      have := charRefl_picB (n := n) i.val hi t
      rw [hv]
      simpa using this
    rw [e, hv, onesCount_picB, onesCount_picB]
    have hswap : (Finset.univ.filter fun k : Fin n => swapAt t i.val k.val = 1) =
        (Finset.univ.filter fun k : Fin n => t k.val = 1).map
          (Equiv.swap i ⟨i.val + 1, hi⟩).toEmbedding := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map_equiv,
        Equiv.symm_swap]
      by_cases h1 : k = i
      · subst h1
        simp [swapAt_left, Equiv.swap_apply_left]
      · by_cases h2 : k = ⟨i.val + 1, hi⟩
        · subst h2
          have : (⟨i.val + 1, hi⟩ : Fin n) ≠ i := fun e => by
            have := congrArg Fin.val e
            simp at this
          simp [swapAt_right, Equiv.swap_apply_right]
        · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
          have h3 : k.val ≠ i.val := fun e => h1 (Fin.ext e)
          have h4 : k.val ≠ i.val + 1 := fun e => h2 (Fin.ext e)
          simp [swapAt_of_ne h3 h4]
    rw [hswap, Finset.card_map]
  · have hn : i.val + 1 = n := by have := i.isLt; omega
    have : charRefl (CartanMatrix.C n) i v = v := by
      funext j
      simp only [charRefl, B_mod2]
      have : ¬ (i.val + 1 = j.val ∨ (j.val + 1 = i.val ∧ i.val + 1 ≠ n)) := by
        have := j.isLt
        omega
      simp [this]
    rw [this]

theorem onesCount_of_charReach {v w : Fin n → ZMod 2} (h : CharReach (CartanMatrix.C n) v w) :
    onesCount w = onesCount v := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
    obtain ⟨i, rfl⟩ := hs
    rw [onesCount_charRefl, ih]

theorem onesCount_single (p₀ : Fin n) : onesCount (Pi.single p₀ (1 : ZMod 2) : Fin n → ZMod 2) =
    p₀.val + 1 := by
  unfold onesCount
  have hs : ∀ k : Fin n, suffixSum (Pi.single p₀ (1 : ZMod 2) : Fin n → ZMod 2) k.val =
      if k.val ≤ p₀.val then 1 else 0 := by
    intro k
    unfold suffixSum
    rw [Finset.sum_eq_single p₀]
    · by_cases h : k.val ≤ p₀.val <;> simp [h]
    · intro j _ hj
      simp [hj]
    · simp
  have : (Finset.univ.filter fun k : Fin n =>
      suffixSum (Pi.single p₀ (1 : ZMod 2) : Fin n → ZMod 2) k.val = 1) =
      Finset.univ.filter fun k : Fin n => k.val ≤ p₀.val := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hs k]
    by_cases h : k.val ≤ p₀.val <;> simp [h]
  rw [this]
  have hc : (Finset.univ.filter fun k : Fin n => k.val ≤ p₀.val) = Finset.Iic p₀ := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic]
    exact Fin.le_iff_val_le_val.symm
  rw [hc, Fin.card_Iic]

theorem card_ones_of_charReach (t : ℕ → ZMod 2) (p₀ : Fin n)
    (h : CharReach (CartanMatrix.C n) (picB n t) (Pi.single p₀ 1)) :
    (Finset.univ.filter fun k : Fin n => t k.val = 1).card = p₀.val + 1 := by
  rw [← onesCount_picB, ← onesCount_single p₀]
  exact (onesCount_of_charReach h).symm

end CFSG.ClassicalInvolution.RouteD.Gaps
