module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.NumberTheory.Multiplicity

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.PLType

@[expose] def fourProd (k : ℕ) : ℕ := ∏ i ∈ Finset.Icc 1 k, (4 ^ i - 1)

theorem fourProd_succ (k : ℕ) : fourProd (k + 1) = fourProd k * (4 ^ (k + 1) - 1) := by
  rw [fourProd, fourProd, Finset.prod_Icc_succ_top (by omega)]

theorem fourProd_pos (k : ℕ) : 0 < fourProd k := by
  induction k with
  | zero => simp [fourProd]
  | succ k ih =>
    rw [fourProd_succ]
    exact Nat.mul_pos ih (Nat.sub_pos_of_lt (Nat.one_lt_pow (by omega) (by norm_num)))

theorem fourProd_odd (k : ℕ) : Odd (fourProd k) := by
  induction k with
  | zero => simp [fourProd]
  | succ k ih =>
    rw [fourProd_succ]
    refine ih.mul ?_
    have : 1 ≤ 4 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
    refine ⟨2 ^ (2 * k + 1) - 1, ?_⟩
    have h2 : 4 ^ (k + 1) = 2 * 2 ^ (2 * k + 1) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_succ']
      ring_nf
    have : 1 ≤ 2 ^ (2 * k + 1) := Nat.one_le_two_pow
    omega

theorem padicValNat_three_fourProd (k : ℕ) :
    padicValNat 3 (fourProd k) = k + padicValNat 3 k.factorial := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  induction k with
  | zero => simp [fourProd]
  | succ k ih =>
    have hne : 4 ^ (k + 1) - 1 ≠ 0 :=
      (Nat.sub_pos_of_lt (Nat.one_lt_pow (by omega) (by norm_num))).ne'
    have hlte : padicValNat 3 (4 ^ (k + 1) - 1) = 1 + padicValNat 3 (k + 1) := by
      have := padicValNat.pow_sub_pow (p := 3) (x := 4) (y := 1) ⟨1, rfl⟩ (by norm_num)
        (by norm_num) (by norm_num) (n := k + 1) (by omega)
      rw [one_pow] at this
      rw [this]
      norm_num
    rw [fourProd_succ, padicValNat.mul (fourProd_pos k).ne' hne, ih, hlte, Nat.factorial_succ,
      padicValNat.mul (by omega) (Nat.factorial_ne_zero k)]
    omega

theorem div_three_le_padicValNat_factorial (n : ℕ) : n / 3 ≤ padicValNat 3 n.factorial := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases Nat.lt_or_ge n 3 with h | h
  · rw [Nat.div_eq_of_lt h]
    exact Nat.zero_le _
  · rw [padicValNat_factorial (b := n + 1) (by
      calc Nat.log 3 n ≤ n := Nat.log_le_self 3 n
        _ < n + 1 := Nat.lt_succ_self n)]
    calc n / 3 = n / 3 ^ 1 := by rw [pow_one]
      _ ≤ ∑ i ∈ Finset.Ico 1 (n + 1), n / 3 ^ i :=
        Finset.single_le_sum (f := fun i => n / 3 ^ i) (fun _ _ => Nat.zero_le _)
          (Finset.mem_Ico.2 ⟨le_rfl, by omega⟩)

theorem two_mul_padicValNat_three_factorial_le (k : ℕ) : 2 * padicValNat 3 k.factorial ≤ k := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := sub_one_mul_padicValNat_factorial (p := 3) k
  norm_num at this
  omega

theorem small_orth_minus :
    ∀ m < 11, 4 ≤ m → ∀ n < 80, 5 ≤ n →
      n.factorial ≠ 2 * (2 ^ (m * (m - 1)) * (2 ^ m - 1) * fourProd (m - 1)) := by
  decide +kernel

theorem small_orth_plus :
    ∀ m < 11, 4 ≤ m → ∀ n < 80, 5 ≤ n →
      n.factorial ≠ 2 * (2 ^ (m * (m - 1)) * (2 ^ m + 1) * fourProd (m - 1)) := by
  decide +kernel

theorem factorial_ne_two_mul_orth {m n A : ℕ} (hm : 4 ≤ m) (hn : 5 ≤ n)
    (hA : A = 2 ^ m - 1 ∨ A = 2 ^ m + 1) :
    n.factorial ≠ 2 * (2 ^ (m * (m - 1)) * A * fourProd (m - 1)) := by
  intro h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2m : 2 ^ 4 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hev : Even (2 ^ m) := Nat.even_pow.2 ⟨even_two, by omega⟩
  have hAodd : Odd A := by
    obtain ⟨k, hk⟩ := hev
    rcases hA with hA | hA
    · exact ⟨k - 1, by omega⟩
    · exact ⟨k, by omega⟩
  have hA3 : A ≤ 3 ^ m := by
    have key : ∀ k, 1 ≤ k → 2 ^ k + 1 ≤ 3 ^ k := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => norm_num
      | succ k hk ih =>
        rw [pow_succ, pow_succ]
        omega
    have := key m (by omega)
    omega
  have hApos : 0 < A := hAodd.pos
  have hPpos := fourProd_pos (m - 1)
  have h2pos : 0 < 2 ^ (m * (m - 1)) := by positivity
  have hAP : 2 ^ (m * (m - 1)) * A * fourProd (m - 1) ≠ 0 :=
    (Nat.mul_pos (Nat.mul_pos h2pos hApos) hPpos).ne'
  have hAP' : 2 ^ (m * (m - 1)) * A ≠ 0 := (Nat.mul_pos h2pos hApos).ne'
  have hv2 : padicValNat 2 n.factorial = m * (m - 1) + 1 := by
    rw [h, padicValNat.mul (by norm_num) hAP, padicValNat.mul hAP' hPpos.ne',
      padicValNat.mul h2pos.ne' hApos.ne', padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hAodd.not_two_dvd_nat,
      padicValNat.eq_zero_of_not_dvd (fourProd_odd _).not_two_dvd_nat]
    simp
    omega
  have hv3 : padicValNat 3 n.factorial =
      padicValNat 3 A + ((m - 1) + padicValNat 3 (m - 1).factorial) := by
    rw [h, padicValNat.mul (by norm_num) hAP, padicValNat.mul hAP' hPpos.ne',
      padicValNat.mul h2pos.ne' hApos.ne', padicValNat_three_fourProd,
      padicValNat.eq_zero_of_not_dvd (p := 3) (n := 2) (by norm_num),
      padicValNat.eq_zero_of_not_dvd (p := 3) (n := 2 ^ (m * (m - 1)))
        (fun hd => by
          have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd)
          omega)]
    omega
  have hvA : padicValNat 3 A ≤ m := by
    have h1 : 3 ^ padicValNat 3 A ∣ A := pow_padicValNat_dvd
    have h2 : 3 ^ padicValNat 3 A ≤ 3 ^ m := (Nat.le_of_dvd hApos h1).trans hA3
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
  have hlt := padicValNat_factorial_lt_of_ne_zero 2 (n := n) (by omega)
  have hlow := div_three_le_padicValNat_factorial n
  have hfac := two_mul_padicValNat_three_factorial_le (m - 1)
  rw [hv2] at hlt
  rw [hv3] at hlow
  by_cases hm10 : m < 11
  · have hn80 : n < 80 := by omega
    rcases hA with rfl | rfl
    · exact small_orth_minus m hm10 hm n hn80 hn h
    · exact small_orth_plus m hm10 hm n hn80 hn h
  · have hmm : 11 * m ≤ m * m := Nat.mul_le_mul_right m (by omega)
    have : m * (m - 1) + m = m * m := by
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    omega

theorem factorial_ne_51840 {n : ℕ} (hn : 5 ≤ n) : n.factorial ≠ 2 * 25920 := by
  intro h
  by_cases h9 : n < 9
  · have : ∀ n < 9, 5 ≤ n → n.factorial ≠ 2 * 25920 := by decide +kernel
    exact this n h9 hn h
  · have : Nat.factorial 9 ≤ n.factorial := Nat.factorial_le (by omega)
    have h9f : Nat.factorial 9 = 362880 := by decide +kernel
    omega

theorem eq_of_two_mul_card_alt {n k : ℕ} (hn : 5 ≤ n) (hk : 5 ≤ k)
    (h : Nat.card (alternatingGroup (Fin n)) = Nat.card (alternatingGroup (Fin k))) : n = k := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.2 (by omega)
  have h1 := two_mul_nat_card_alternatingGroup (α := Fin n)
  have h2 := two_mul_nat_card_alternatingGroup (α := Fin k)
  rw [h] at h1
  simp only [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at h1 h2
  exact (Nat.factorial_inj (by omega)).1 (h1.symm.trans h2)

end CFSG.HardMathSupport.Curtis.Coordinator.PLType
