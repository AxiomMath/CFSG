module

public import CFSG.Certificates.Kernel.O8EnumDefs

public section

namespace CFSG.KC.O8

open CFSG.KLie.CT CFSG.KC.Loop CFSG.EvenSmallLie.OmegaEight.Stage2

private theorem strictN_eqF (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by
  cases y <;> rfl

private theorem blt_t {a b : ℕ} (h : a < b) : Nat.blt a b = true := by simpa using h

private theorem blt_f {a b : ℕ} (h : ¬ a < b) : Nat.blt a b = false := by
  cases e : Nat.blt a b
  · rfl
  · exact absurd (by simpa using e) h

private theorem beq_t {a b : ℕ} (h : a = b) : Nat.beq a b = true := by simpa using h

private theorem beq_f {a b : ℕ} (h : ¬ a = b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

private theorem enFind_succ(D : Nat → Nat) (k f lo hi : Nat) :
    enFind D k (f + 1) lo hi =
      if lo < hi then
        (if enKey D ((lo + hi) / 2) = k then 1
        else if enKey D ((lo + hi) / 2) < k then enFind D k f ((lo + hi) / 2 + 1) hi
        else enFind D k f lo ((lo + hi) / 2))
      else 0 := by
  have e0 : enFind D k (f + 1) lo hi =
      Bool.rec (motive := fun _ => Nat) 0
        (strictN ((lo + hi) / 2) fun mid => strictN (enKey D mid) fun K =>
          Bool.rec (motive := fun _ => Nat)
            (Bool.rec (motive := fun _ => Nat) (enFind D k f lo mid) (enFind D k f (mid + 1) hi)
              (Nat.blt K k))
            1 (Nat.beq K k))
        (Nat.blt lo hi) := rfl
  rw [e0, strictN_eqF, strictN_eqF]
  by_cases h1 : lo < hi
  · rw [blt_t h1]
    by_cases h2 : enKey D ((lo + hi) / 2) = k
    · rw [beq_t h2]
      simp [h1, h2]
    · rw [beq_f h2]
      by_cases h3 : enKey D ((lo + hi) / 2) < k
      · rw [blt_t h3]
        simp [h1, h2, h3]
      · rw [blt_f h3]
        simp [h1, h2, h3]
  · rw [blt_f h1]
    simp [h1]

private theorem enFind_sound (D : Nat → Nat) (k : Nat) : ∀ f lo hi, enFind D k f lo hi = 1 →
    ∃ i, lo ≤ i ∧ i < hi ∧ enKey D i = k
  | 0, lo, hi, h => by
    have : enFind D k 0 lo hi = 0 := rfl
    rw [this] at h
    exact absurd h (by decide)
  | f + 1, lo, hi, h => by
    rw [enFind_succ] at h
    by_cases h1 : lo < hi
    · simp only [h1, ↓reduceIte] at h
      by_cases h2 : enKey D ((lo + hi) / 2) = k
      · exact ⟨(lo + hi) / 2, by omega, by omega, h2⟩
      · simp only [h2, ↓reduceIte] at h
        by_cases h3 : enKey D ((lo + hi) / 2) < k
        · simp only [h3, ↓reduceIte] at h
          obtain ⟨i, hi1, hi2, hi3⟩ := enFind_sound D k f _ _ h
          exact ⟨i, by omega, hi2, hi3⟩
        · simp only [h3, ↓reduceIte] at h
          obtain ⟨i, hi1, hi2, hi3⟩ := enFind_sound D k f _ _ h
          exact ⟨i, hi1, by omega, hi3⟩
    · simp [h1] at h

private theorem enFind_complete (D : Nat → Nat) (k N : Nat)
    (hs : ∀ i j, i < j → j < N → enKey D i < enKey D j) : ∀ f lo hi, hi ≤ N → hi - lo < 2 ^ f →
      ∀ i, lo ≤ i → i < hi → enKey D i = k → enFind D k f lo hi = 1
  | 0, lo, hi, _, hf, i, h1, h2, _ => by
    simp at hf
    omega
  | f + 1, lo, hi, hN, hf, i, h1, h2, hk => by
    rw [enFind_succ]
    have hlh : lo < hi := by omega
    simp only [hlh, ↓reduceIte]
    have hp : 2 ^ (f + 1) = 2 * 2 ^ f := by rw [Nat.pow_succ, Nat.mul_comm]
    by_cases h3 : enKey D ((lo + hi) / 2) = k
    · simp [h3]
    · simp only [h3, ↓reduceIte]
      by_cases h4 : enKey D ((lo + hi) / 2) < k
      · simp only [h4, ↓reduceIte]
        have hmi : (lo + hi) / 2 < i := by
          by_contra hc
          rcases Nat.lt_or_ge i ((lo + hi) / 2) with hc' | hc'
          · have := hs _ _ hc' (by omega)
            omega
          · have : i = (lo + hi) / 2 := by omega
            subst this
            exact h3 hk
        exact enFind_complete D k N hs f _ _ hN (by omega) i (by omega) h2 hk
      · simp only [h4, ↓reduceIte]
        have hmi : i < (lo + hi) / 2 := by
          by_contra hc
          rcases Nat.lt_or_ge ((lo + hi) / 2) i with hc' | hc'
          · have := hs _ _ hc' (by omega)
            omega
          · have : i = (lo + hi) / 2 := by omega
            subst this
            exact h3 hk
        exact enFind_complete D k N hs f _ _ (by omega) (by omega) i h1 hmi hk

theorem exists_of_enMemK_proved {D : Nat → Nat} {m k : Nat} (h : enMemK D m k = true) :
    ∃ i < m, enKey D i = k := by
  have h1 : enFind D k 18 0 m = 1 := Nat.eq_of_beq_eq_true h
  obtain ⟨i, _, hi, hk⟩ := enFind_sound D k 18 0 m h1
  exact ⟨i, hi, hk⟩

theorem memK_decE_eq_proved {D : Nat → Nat} {m : Nat} (hs : sortedK (decE D m).keys = true)
    (hm : m < 2 ^ 17) (k : ℕ) : memK (decE D m).keys k = enMemK D m k := by
  apply Bool.eq_iff_iff.2
  constructor
  · intro h
    obtain ⟨i, hi, hk⟩ := exists_of_memK h
    rw [decE_keys_size] at hi
    rw [decE_keys_getD hi] at hk
    have hs' : ∀ i j, i < j → j < m → enKey D i < enKey D j := by
      intro i j hij hj
      have := Enum.lt_of_sortedK hs hij (by rwa [decE_keys_size])
      rwa [decE_keys_getD (by omega), decE_keys_getD hj] at this
    have h18 : m - 0 < 2 ^ 18 := by omega
    exact beq_t (enFind_complete D k m hs' 18 0 m (Nat.le_refl m) h18 i (Nat.zero_le i) hi hk)
  · intro h
    obtain ⟨i, hi, hk⟩ := exists_of_enMemK_proved h
    exact memK_of_mem hs (by rw [decE_keys_size]; omega) (by rwa [decE_keys_size])
      (by rw [decE_keys_getD hi]; exact hk)

end CFSG.KC.O8

end
