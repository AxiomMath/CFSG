module

public import CFSG.Open.Defs
public import CFSG.HardMathSupport.Lang.AnisoF4.B4ModFacts

public section

namespace CFSG.HardMathSupport.Lang.AnisoF4



theorem factorization_ordF4_le_ordBC {P q : ℕ} (hP : P.Prime) (hP5 : 5 ≤ P) (hq : 2 ≤ q)
    (hd : P ∣ q ^ 2 + 1) :
    (CFSG.Open.ordF4 q).factorization P ≤ (CFSG.Open.ordBC 4 q).factorization P := by
  have hq1 : 1 ≤ q := by omega
  obtain ⟨hpq, h2, h6, hndvd⟩ := notDvd_facts hP hP5 hq1 hd
  have hqpos : ∀ k : ℕ, 1 ≤ q ^ k := fun k => Nat.one_le_pow _ _ (by omega)
  have hqlt : ∀ k : ℕ, 0 < k → 1 < q ^ k := fun k hk => Nat.one_lt_pow hk.ne' (by omega)
  have hnz : ∀ k : ℕ, 0 < k → q ^ k - 1 ≠ 0 := fun k hk => by
    have := hqlt k hk
    omega
  have hf0 : ∀ n : ℕ, ¬ P ∣ n → n.factorization P = 0 := fun n h =>
    Nat.factorization_eq_zero_of_not_dvd h
  have hdiv12 : (q ^ 12 - 1) = (q ^ 4 - 1) * (q ^ 8 + q ^ 4 + 1) := by
    have h1 : 1 ≤ q ^ 4 := hqpos 4
    zify [h1, hqpos 12]
    ring
  have hf12 : (q ^ 12 - 1).factorization P = (q ^ 4 - 1).factorization P := by
    rw [hdiv12, Nat.factorization_mul (hnz 4 (by norm_num))
      (by positivity), Finsupp.add_apply, hf0 _ hndvd, add_zero]
  have hF4 : (CFSG.Open.ordF4 q).factorization P = (q ^ 12 - 1).factorization P +
      (q ^ 8 - 1).factorization P := by
    unfold CFSG.Open.ordF4
    rw [Nat.factorization_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero (by positivity)
      (hnz 12 (by norm_num))) (hnz 8 (by norm_num))) (hnz 6 (by norm_num))) (hnz 2 (by norm_num)),
      Finsupp.add_apply, hf0 _ h2, add_zero,
      Nat.factorization_mul (mul_ne_zero (mul_ne_zero (by positivity)
      (hnz 12 (by norm_num))) (hnz 8 (by norm_num))) (hnz 6 (by norm_num)),
      Finsupp.add_apply, hf0 _ h6, add_zero,
      Nat.factorization_mul (mul_ne_zero (by positivity)
      (hnz 12 (by norm_num))) (hnz 8 (by norm_num)),
      Finsupp.add_apply,
      Nat.factorization_mul (by positivity) (hnz 12 (by norm_num)),
      Finsupp.add_apply, hf0 _ (hpq 24), zero_add]
  have hprod : ∏ i ∈ Finset.Icc 1 4, (q ^ (2 * i) - 1) =
      (q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) * (q ^ 8 - 1) := by
    simp [Finset.prod_Icc_succ_top]
  set N := q ^ (4 * 4) * ∏ i ∈ Finset.Icc 1 4, (q ^ (2 * i) - 1) with hN
  have hNnz : N ≠ 0 := by
    rw [hN, hprod]
    exact mul_ne_zero (by positivity) (mul_ne_zero (mul_ne_zero (mul_ne_zero (hnz 2 (by norm_num))
      (hnz 4 (by norm_num))) (hnz 6 (by norm_num))) (hnz 8 (by norm_num)))
  have hNf : N.factorization P = (q ^ 4 - 1).factorization P + (q ^ 8 - 1).factorization P := by
    rw [hN, hprod, Nat.factorization_mul (by positivity)
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (hnz 2 (by norm_num))
      (hnz 4 (by norm_num))) (hnz 6 (by norm_num))) (hnz 8 (by norm_num))),
      Finsupp.add_apply, hf0 _ (by simpa using hpq (4 * 4)), zero_add,
      Nat.factorization_mul (mul_ne_zero (mul_ne_zero (hnz 2 (by norm_num))
      (hnz 4 (by norm_num))) (hnz 6 (by norm_num))) (hnz 8 (by norm_num)),
      Finsupp.add_apply,
      Nat.factorization_mul (mul_ne_zero (hnz 2 (by norm_num))
      (hnz 4 (by norm_num))) (hnz 6 (by norm_num)),
      Finsupp.add_apply, hf0 _ h6, add_zero,
      Nat.factorization_mul (hnz 2 (by norm_num)) (hnz 4 (by norm_num)),
      Finsupp.add_apply, hf0 _ h2, zero_add]
  have hg : Nat.gcd 2 (q - 1) ∣ N := by
    have h1 : Nat.gcd 2 (q - 1) ∣ q - 1 := Nat.gcd_dvd_right _ _
    have h2' : q - 1 ∣ q ^ 2 - 1 := by
      simpa using Nat.sub_dvd_pow_sub_pow q 1 2
    have h3 : q ^ 2 - 1 ∣ N := by
      rw [hN, hprod]
      exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right
        (dvd_refl _) _) _) _) _
    exact h1.trans (h2'.trans h3)
  have hgf : (Nat.gcd 2 (q - 1)).factorization P = 0 := by
    apply hf0
    intro hdv
    have := Nat.le_of_dvd (by norm_num) (hdv.trans (Nat.gcd_dvd_left 2 (q - 1)))
    omega
  have hBC : (CFSG.Open.ordBC 4 q).factorization P = N.factorization P := by
    have hg0 : Nat.gcd 2 (q - 1) ≠ 0 := (Nat.gcd_pos_of_pos_left _ (by norm_num)).ne'
    have : CFSG.Open.ordBC 4 q = N / Nat.gcd 2 (q - 1) := by
      rw [CFSG.Open.ordBC, hN]
    rw [this, Nat.factorization_div hg, Finsupp.coe_tsub, Pi.sub_apply, hgf, Nat.sub_zero]
  rw [hBC, hNf, hF4, hf12]

end CFSG.HardMathSupport.Lang.AnisoF4
