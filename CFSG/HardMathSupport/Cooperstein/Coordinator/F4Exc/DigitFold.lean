module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc.DigitFoldArith
public import CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc.DigitFoldData
public import CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc.OneDigit

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc

open CFSG.Blueprint.Chevalley

theorem not_dvd_minors_le_six {x y : Fin Tag.F4.rank → ℤ}
    (h : 1 ≤ contentL (minorsL (List.ofFn x) (List.ofFn y)) ∧
      contentL (minorsL (List.ofFn x) (List.ofFn y)) ≤ 6) (d : ℕ) (hd : 7 ≤ d) :
    ¬ ∀ c c', (d : ℤ) ∣ minorF x y c c' := by
  intro hc
  have h1 : d ∣ contentL (minorsL (List.ofFn x) (List.ofFn y)) := by
    refine dvd_contentL d _ fun z hz => ?_
    simp only [minorsL, List.mem_cons, List.not_mem_nil, or_false] at hz
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hc (f4n 0) (f4n 1)
      | exact hc (f4n 0) (f4n 2)
      | exact hc (f4n 0) (f4n 3)
      | exact hc (f4n 1) (f4n 2)
      | exact hc (f4n 1) (f4n 3)
      | exact hc (f4n 2) (f4n 3)
  have := Nat.le_of_dvd (by omega) h1
  omega

theorem dvd_of_mul_gamD {M : ℕ} (hM2 : IsCoprime (M : ℤ) 2) {ε : Fin Tag.F4.rank → ℤ}
    (hc : 1 ≤ contentL (List.ofFn ε) ∧ contentL (List.ofFn ε) ≤ 2) {m : ℤ}
    (h : ∀ c, (M : ℤ) ∣ m * ε c) : (M : ℤ) ∣ m := by
  have h1 : M ∣ m.natAbs * contentL (List.ofFn ε) := by
    refine dvd_mul_contentL M m.natAbs _ fun z hz => ?_
    rw [List.mem_ofFn] at hz
    obtain ⟨c, rfl⟩ := hz
    rw [Int.natCast_natAbs]
    rcases abs_choice m with e | e
    · rw [e]; exact h c
    · rw [e, neg_mul, dvd_neg]; exact h c
  have h2 : (M : ℤ) ∣ |m| := by
    rcases (by omega : contentL (List.ofFn ε) = 1 ∨ contentL (List.ofFn ε) = 2) with h3 | h3
    · rw [h3, mul_one] at h1
      have := Int.natCast_dvd_natCast.2 h1
      rwa [Int.natCast_natAbs] at this
    · rw [h3] at h1
      have := Int.natCast_dvd_natCast.2 h1
      push_cast at this
      exact hM2.dvd_of_dvd_mul_right this
  exact (dvd_abs _ _).1 h2

theorem three_of_pair {M : ℕ}
    (hM7 : 7 ≤ M) (hM2 : IsCoprime (M : ℤ) 2) {t : ℤ} (ht : IsCoprime (M : ℤ) t) {a : ℤ}
    {s : Fin Tag.F4.rank} (hs : s.val = 0 ∨ s.val = 3) {i i' : Fin 12} (hii : i ≠ i')
    {j j' : Fin 8} (h : ∀ k : Fin Tag.F4.rank, (M : ℤ) ∣ a * betaD s i i' j j' k - t * gamD s i i' k) :
    (M : ℤ) ∣ a - t ∨ (M : ℤ) ∣ a + t ∨ (M : ℤ) ∣ 2 * a - t := by
  rcases pair_cases s hs i i' hii j j' with hm | ⟨hc1, hc2, hrel⟩
  · exfalso
    refine not_dvd_minors_le_six hm M hM7 fun c c' => ?_
    have h1 : (M : ℤ) ∣ t * minorF (betaD s i i' j j') (gamD s i i') c c' := by
      have e : t * minorF (betaD s i i' j j') (gamD s i i') c c' =
          betaD s i i' j j' c' * (a * betaD s i i' j j' c - t * gamD s i i' c) -
          betaD s i i' j j' c * (a * betaD s i i' j j' c' - t * gamD s i i' c') := by
        unfold minorF; ring
      rw [e]
      exact dvd_sub (dvd_mul_of_dvd_right (h c) _) (dvd_mul_of_dvd_right (h c') _)
    exact ht.dvd_of_dvd_mul_left h1
  · have hc : 1 ≤ contentL (List.ofFn (gamD s i i')) ∧ contentL (List.ofFn (gamD s i i')) ≤ 2 :=
      ⟨hc1, hc2⟩
    rcases hrel with hd | hd | hd | hd
    · left
      refine dvd_of_mul_gamD hM2 hc fun c => ?_
      have := h c
      rw [hd c] at this
      convert this using 1; ring
    · right; left
      refine dvd_of_mul_gamD hM2 hc fun c => ?_
      have := (dvd_neg).2 (h c)
      rw [hd c] at this
      convert this using 1; ring
    · right; right
      refine dvd_of_mul_gamD hM2 hc fun c => ?_
      have := h c
      rw [hd c] at this
      convert this using 1; ring
    · exfalso
      have h1 : (M : ℤ) ∣ t := by
        refine dvd_of_mul_gamD hM2 hc fun c => ?_
        have := (dvd_neg).2 (h c)
        rw [hd c] at this
        convert this using 1; ring
      have h2 : (M : ℤ) ∣ 1 := ht.dvd_of_dvd_mul_right (by simpa using h1)
      have := Int.le_of_dvd (by norm_num) h2
      have h7 : (7 : ℤ) ≤ M := by exact_mod_cast hM7
      omega

theorem exists_digit_fold
    {s : Fin Tag.F4.rank} (hs : s.val = 0 ∨ s.val = 3) {f : ℕ} (hf : 3 ≤ f)
    (J' : Finset ℕ) (hJ' : ∀ i ∈ J', i < 2 * f) (hc : 2 ≤ J'.card) :
    ∃ dg ∈ J', ∀ (i i' : Fin 12), i ≠ i' → ∀ (j j' : Fin 8),
      ¬ ∀ k : Fin Tag.F4.rank, (((2 ^ f - 1 : ℕ)) : ℤ) ∣
        ((∑ b ∈ J', 2 ^ b : ℕ) : ℤ) * ((wF s i • (uF s j • f4Omega s)) k - (wF s i' • (uF s j' • f4Omega s)) k)
          - 2 ^ dg * ((wF s i • (Pi.single s (1 : ℤ) : Fin Tag.F4.rank → ℤ)) k
              - (wF s i' • (Pi.single s (1 : ℤ) : Fin Tag.F4.rank → ℤ)) k) := by
  obtain ⟨dg, hdg, h1, h2, h3⟩ := exists_good_digit hf J' hJ' hc
  refine ⟨dg, hdg, fun i i' hii j j' hdiv => ?_⟩
  have hβ : ∀ (i j : ℕ) (k : Fin Tag.F4.rank), (betaL s i j).getD k 0 =
      (wF s i • (uF s j • f4Omega s)) k := fun i j k => by
    rw [← ofFn_wF_uF_Omega, getD_ofFn4]
  have hγ : ∀ (i : ℕ) (k : Fin Tag.F4.rank), (gamL s i).getD k 0 =
      (wF s i • (Pi.single s (1 : ℤ) : Fin Tag.F4.rank → ℤ)) k := fun i k => by
    rw [← ofFn_wF_single, getD_ofFn4]
  have eM : (((2 ^ f - 1 : ℕ)) : ℤ) = 2 ^ f - 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; ring
  have ea : ((∑ b ∈ J', 2 ^ b : ℕ) : ℤ) = ∑ b ∈ J', (2 : ℤ) ^ b := by push_cast; rfl
  have hM7 : 7 ≤ 2 ^ f - 1 := by
    have : 2 ^ 3 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  have hcop := odd_coprime f (by omega)
  have hdiv' : ∀ k : Fin Tag.F4.rank, (((2 ^ f - 1 : ℕ)) : ℤ) ∣
      ((∑ b ∈ J', 2 ^ b : ℕ) : ℤ) * betaD s i i' j j' k - 2 ^ dg * gamD s i i' k := by
    intro k
    have := hdiv k
    rw [← hβ i j k, ← hβ i' j' k, ← hγ i k, ← hγ i' k] at this
    exact this
  have hM2 : IsCoprime (((2 ^ f - 1 : ℕ)) : ℤ) 2 := by simpa using hcop 1
  rcases three_of_pair (M := 2 ^ f - 1) (a := ((∑ b ∈ J', 2 ^ b : ℕ) : ℤ)) hM7 hM2 (hcop dg) hs hii
      hdiv' with h | h | h
  · rw [eM, ea] at h; exact h1 h
  · rw [eM, ea] at h; exact h2 h
  · rw [eM, ea] at h; exact h3 h

end CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc
