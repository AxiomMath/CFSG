module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc.Pairs

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CoxeterSystem

theorem key_arith {n d : ℕ} (hn : 7 ≤ n) (hd1 : 1 ≤ d) (h2d : 2 * d ≤ n) {x y : ℤ} (hx : |x| ≤ 8)
    (hy : |y| ≤ 8) (h : (((2 ^ n - 1 : ℕ)) : ℤ) ∣ (1 + 2 ^ d) * x - y) : (1 + 2 ^ d) * x = y := by
  have hX : (2 : ℤ) ^ d * 2 ^ d ≤ 2 ^ n := by
    rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) (by omega)
  have h128 : (128 : ℤ) ≤ 2 ^ n := by
    calc (128 : ℤ) = 2 ^ 7 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have hX2 : (2 : ℤ) ≤ 2 ^ d := by
    calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) hd1
  have hM : |(1 + 2 ^ d) * x - y| < (((2 ^ n - 1 : ℕ)) : ℤ) := by
    have e : (((2 ^ n - 1 : ℕ)) : ℤ) = 2 ^ n - 1 := by
      rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; ring
    rw [e]
    have h1 : |(1 + 2 ^ d) * x - y| ≤ (1 + 2 ^ d) * 8 + 8 := by
      calc |(1 + 2 ^ d) * x - y| ≤ |(1 + 2 ^ d) * x| + |y| := abs_sub _ _
        _ = (1 + 2 ^ d) * |x| + |y| := by rw [abs_mul, abs_of_pos (by positivity)]
        _ ≤ (1 + 2 ^ d) * 8 + 8 := by gcongr
    have h2 : (1 + (2 : ℤ) ^ d) * 8 + 8 < 2 ^ n - 1 := by
      rcases le_or_gt ((2 : ℤ) ^ d) 13 with h13 | h13
      · nlinarith
      · nlinarith
    linarith
  have := Int.eq_zero_of_abs_lt_dvd h hM
  linarith

theorem finish_arith {d : ℕ} (hd1 : 1 ≤ d) (δ ε : Fin 4 → ℤ) (hε : ∀ k, |ε k| ≤ 8)
    (heq : ∀ k, (1 + 2 ^ d) * δ k = ε k) :
    (∀ k, ε k = 0) ∨ ∃ cc ∈ ([3, 5] : List ℤ), ∀ k, cc * δ k = ε k := by
  rcases Nat.lt_or_ge d 3 with hd | hd
  · right
    have : d = 1 ∨ d = 2 := by omega
    rcases this with rfl | rfl
    · exact ⟨3, by simp, fun k => by rw [← heq k]; norm_num⟩
    · exact ⟨5, by simp, fun k => by rw [← heq k]; norm_num⟩
  · left
    have h8 : (8 : ℤ) ≤ 2 ^ d := by
      calc (8 : ℤ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) hd
    intro k
    by_cases hk : δ k = 0
    · rw [← heq k, hk]; simp
    · exfalso
      have h1 : 1 ≤ |δ k| := Int.one_le_abs hk
      have h2 := hε k
      rw [← heq k, abs_mul, abs_of_pos (by positivity)] at h2
      nlinarith

theorem odd_coprime (n : ℕ) (hn : 1 ≤ n) (b : ℕ) : IsCoprime (((2 ^ n - 1 : ℕ)) : ℤ) ((2 : ℤ) ^ b) := by
  refine IsCoprime.pow_right ?_
  have : Odd (2 ^ n - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact ⟨2 ^ m - 1, by have := Nat.one_le_two_pow (n := m); rw [pow_succ]; omega⟩
  obtain ⟨k, hk⟩ := this
  rw [hk]
  exact ⟨1, -(k : ℤ), by push_cast; ring⟩

theorem gen_sep {n b c : ℕ} (hn : 7 ≤ n) (hbc : b < c) (hcn : c < n) {dg : ℕ}
    (hdg : dg = if c - b ≤ n - (c - b) then b else c)
    (δ ε : Fin 4 → ℤ) (hδ : ∀ k, |δ k| ≤ 8) (hε : ∀ k, |ε k| ≤ 8)
    (h : ∀ k, (((2 ^ n - 1 : ℕ)) : ℤ) ∣ ((2 : ℤ) ^ b + 2 ^ c) * δ k - 2 ^ dg * ε k) :
    (∀ k, ε k = 0) ∨ ∃ cc ∈ ([3, 5] : List ℤ), ∀ k, cc * δ k = ε k := by
  obtain ⟨d, hd⟩ : ∃ d, c = b + d := ⟨c - b, by omega⟩
  have hd1 : 1 ≤ d := by omega
  have e : (2 : ℤ) ^ b + 2 ^ c = 2 ^ b * (1 + 2 ^ d) := by rw [hd, pow_add]; ring
  have hcop := odd_coprime n (by omega) b
  by_cases hdn : d ≤ n - d
  · have hdg' : dg = b := by rw [hdg, if_pos (by omega)]
    subst hdg'
    refine finish_arith hd1 δ ε hε fun k => ?_
    refine key_arith hn hd1 (by omega) (hδ k) (hε k) ?_
    have := h k
    rw [e] at this
    have h2 : (((2 ^ n - 1 : ℕ)) : ℤ) ∣ (2 : ℤ) ^ dg * ((1 + 2 ^ d) * δ k - ε k) := by
      convert this using 1; ring
    exact hcop.dvd_of_dvd_mul_left h2
  · have hdg' : dg = c := by rw [hdg, if_neg (by omega)]
    subst hdg'
    obtain ⟨d', hd'⟩ : ∃ d', n = d + d' := ⟨n - d, by omega⟩
    have hd'1 : 1 ≤ d' := by omega
    have h2d' : 2 * d' ≤ n := by omega
    have hq : ∀ k, (((2 ^ n - 1 : ℕ)) : ℤ) ∣ (1 + 2 ^ d') * δ k - ε k := by
      intro k
      have h1 := h k
      rw [e] at h1
      have h2 : (((2 ^ n - 1 : ℕ)) : ℤ) ∣ (2 : ℤ) ^ b * ((1 + 2 ^ d) * δ k - 2 ^ d * ε k) := by
        convert h1 using 1; rw [hd, pow_add]; ring
      have h3 := hcop.dvd_of_dvd_mul_left h2
      have h4 : (((2 ^ n - 1 : ℕ)) : ℤ) ∣ 2 ^ d' * ((1 + 2 ^ d) * δ k - 2 ^ d * ε k) :=
        dvd_mul_of_dvd_right h3 _
      have hM : (((2 ^ n - 1 : ℕ)) : ℤ) = 2 ^ n - 1 := by
        rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; ring
      have h5 : (1 + (2 : ℤ) ^ d') * δ k - ε k =
          2 ^ d' * ((1 + 2 ^ d) * δ k - 2 ^ d * ε k) - (((2 ^ n - 1 : ℕ)) : ℤ) * (δ k - ε k) := by
        rw [hM, hd']
        simp only [pow_add]
        ring
      rw [h5]
      exact dvd_sub h4 (dvd_mul_right _ _)
    refine finish_arith hd'1 δ ε hε fun k => ?_
    exact key_arith hn hd'1 h2d' (hδ k) (hε k) (hq k)

theorem getD_ofFn4 (v : Fin Tag.F4.rank → ℤ) (k : Fin Tag.F4.rank) : (List.ofFn v).getD k 0 = v k := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn]

theorem vclassEq_false {M a dg : ℕ} {β β' γ γ' : List ℤ}
    (h : vclassEq M a dg β β' γ γ' = false) :
    ∃ k < 4, ¬ ((M : ℤ) ∣ (a : ℤ) * (β.getD k 0 - β'.getD k 0) -
      (2 : ℤ) ^ dg * (γ.getD k 0 - γ'.getD k 0)) := by
  simp only [vclassEq, Bool.eq_false_iff, ne_eq, List.all_eq_true, List.mem_range, beq_iff_eq,
    not_forall] at h
  obtain ⟨k, hk, hk2⟩ := h
  exact ⟨k, hk, fun hd => hk2 (Int.emod_eq_zero_of_dvd hd)⟩

theorem exists_digit
    {s : Fin Tag.F4.rank} (hs : s.val = 0 ∨ s.val = 3) {n b c : ℕ} (hn : 2 ≤ n) (hbc : b < c)
    (hcn : c < n) :
    ∃ dg, (dg = b ∨ dg = c) ∧ ∀ (i i' : Fin 12), i ≠ i' → ∀ (j j' : Fin 8),
      ¬ ∀ k : Fin Tag.F4.rank, (((2 ^ n - 1 : ℕ)) : ℤ) ∣ ((2 : ℤ) ^ b + 2 ^ c) *
        ((wF s i • (uF s j • f4Omega s)) k - (wF s i' • (uF s j' • f4Omega s)) k) -
        2 ^ dg * ((wF s i • (Pi.single s (1 : ℤ) : Fin Tag.F4.rank → ℤ)) k -
          (wF s i' • (Pi.single s (1 : ℤ) : Fin Tag.F4.rank → ℤ)) k) := by
  have hβ : ∀ (i j : ℕ) (k : Fin Tag.F4.rank), (betaL s i j).getD k 0 =
      (wF s i • (uF s j • f4Omega s)) k := fun i j k => by
    rw [← ofFn_wF_uF_Omega, getD_ofFn4]
  have hγ : ∀ (i : ℕ) (k : Fin Tag.F4.rank), (gamL s i).getD k 0 =
      (wF s i • (Pi.single s (1 : ℤ) : Fin Tag.F4.rank → ℤ)) k := fun i k => by
    rw [← ofFn_wF_single, getD_ofFn4]
  by_cases hn7 : 7 ≤ n
  · refine ⟨if c - b ≤ n - (c - b) then b else c, by split_ifs <;> simp, ?_⟩
    intro i i' hii j j' hdiv
    have hb := pair_bound s hs i i' j j'
    have hδ : ∀ k, |(wF s i • (uF s j • f4Omega s)) k - (wF s i' • (uF s j' • f4Omega s)) k| ≤ 8 := by
      intro k
      have := (hb k).1
      rw [hβ, hβ] at this
      rw [Int.abs_eq_natAbs]; exact_mod_cast this
    have hε : ∀ k, |(wF s i • (Pi.single s (1 : ℤ) : Fin Tag.F4.rank → ℤ)) k -
        (wF s i' • (Pi.single s (1 : ℤ) : Fin Tag.F4.rank → ℤ)) k| ≤ 8 := by
      intro k
      have := (hb k).2
      rw [hγ, hγ] at this
      rw [Int.abs_eq_natAbs]; exact_mod_cast this
    rcases gen_sep hn7 hbc hcn rfl
        (fun k => (wF s i • (uF s j • f4Omega s)) k - (wF s i' • (uF s j' • f4Omega s)) k)
        (fun k => (wF s i • (Pi.single s (1 : ℤ) : Fin Tag.F4.rank → ℤ)) k -
          (wF s i' • (Pi.single s (1 : ℤ) : Fin Tag.F4.rank → ℤ)) k) hδ hε
        (fun k => hdiv k) with h0 | ⟨cc, hcc, hmul⟩
    · apply gamL_ne s i i' hii
      rw [← ofFn_wF_single, ← ofFn_wF_single]
      congr 1
      funext k
      have := h0 k
      linarith
    · apply pair_no_mult s hs i i' hii j j' cc hcc
      intro k
      have := hmul k
      rw [hβ, hβ, hγ, hγ]
      exact this
  · have hnl : n ∈ ([2, 3, 4, 5, 6] : List ℕ) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; omega
    rcases small_sep hs hnl (by omega) hcn hbc with h | h
    · refine ⟨b, Or.inl rfl, ?_⟩
      intro i i' hii j j' hdiv
      obtain ⟨k, hk4, hk⟩ := vclassEq_false (digitOK_sound h i i' hii j j')
      apply hk
      have h3 := hdiv ⟨k, hk4⟩
      rw [hβ i j ⟨k, hk4⟩, hβ i' j' ⟨k, hk4⟩, hγ i ⟨k, hk4⟩, hγ i' ⟨k, hk4⟩]
      push_cast
      exact h3
    · refine ⟨c, Or.inr rfl, ?_⟩
      intro i i' hii j j' hdiv
      obtain ⟨k, hk4, hk⟩ := vclassEq_false (digitOK_sound h i i' hii j j')
      apply hk
      have h3 := hdiv ⟨k, hk4⟩
      rw [hβ i j ⟨k, hk4⟩, hβ i' j' ⟨k, hk4⟩, hγ i ⟨k, hk4⟩, hγ i' ⟨k, hk4⟩]
      push_cast
      exact h3

end CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc
