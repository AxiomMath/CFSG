module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I114Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I91T5

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I114

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.GLTheoremB

private theorem sfm8_three_mul_ordA {x : ℕ} (hx : x % 3 = 1) :
    3 * CFSG.Open.ordA 2 x = x ^ 3 * (x ^ 2 - 1) * (x ^ 3 - 1) := by
  have h3 : 3 ∣ x - 1 := by omega
  have hg : Nat.gcd (2 + 1) (x - 1) = 3 := Nat.gcd_eq_left h3
  have hprod : ∏ i ∈ Finset.Icc 2 (2 + 1), (x ^ i - 1) = (x ^ 2 - 1) * (x ^ 3 - 1) := by
    rw [show Finset.Icc 2 (2 + 1) = {2, 3} from by decide, Finset.prod_pair (by norm_num)]
  have hcube : x ^ 3 % 3 = 1 := by
    simp [Nat.pow_mod, hx]
  have h3' : 3 ∣ x ^ 3 - 1 := by omega
  have hdvd : 3 ∣ x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 - 1)) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_left h3' _) _
  unfold CFSG.Open.ordA
  rw [hg, hprod, show 2 * (2 + 1) / 2 = 3 from rfl, Nat.mul_div_cancel' hdvd]
  ring

private theorem sfm8_two_pow_mod_three {k : ℕ} (hk : Even k) : 2 ^ k % 3 = 1 := by
  obtain ⟨j, rfl⟩ := hk
  rw [← two_mul, pow_mul]
  norm_num [Nat.pow_mod]

private theorem sfm8_gl3_mono {a b : ℕ} (h : a ≤ b) :
    a ^ 3 * (a ^ 2 - 1) * (a ^ 3 - 1) ≤ b ^ 3 * (b ^ 2 - 1) * (b ^ 3 - 1) :=
  Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left h 3)
    (Nat.sub_le_sub_right (Nat.pow_le_pow_left h 2) 1))
    (Nat.sub_le_sub_right (Nat.pow_le_pow_left h 3) 1)

private theorem sfm8_gl3_lt_su3 {q : ℕ} (hq : 2 ≤ q) :
    q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) < q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) := by
  have hq2 : 4 ≤ q ^ 2 := by nlinarith
  have hpos : 0 < q ^ 3 * (q ^ 2 - 1) := Nat.mul_pos (by positivity) (by omega)
  exact Nat.mul_lt_mul_of_pos_left (by omega) hpos

private theorem sfm8_su3_lt_gl3_succ {q : ℕ} (hq : 2 ≤ q) :
    q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) < (q + 1) ^ 3 * ((q + 1) ^ 2 - 1) * ((q + 1) ^ 3 - 1) := by
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hA : q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) < q ^ 3 * q ^ 2 * (q ^ 3 + 1) := by
    have hlt : q ^ 2 - 1 < q ^ 2 := by omega
    have hpos : 0 < q ^ 3 * (q ^ 3 + 1) := by positivity
    calc q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) = (q ^ 2 - 1) * (q ^ 3 * (q ^ 3 + 1)) := by ring
      _ < q ^ 2 * (q ^ 3 * (q ^ 3 + 1)) := Nat.mul_lt_mul_of_pos_right hlt hpos
      _ = q ^ 3 * q ^ 2 * (q ^ 3 + 1) := by ring
  have hB : q ^ 3 * q ^ 2 * (q ^ 3 + 1) ≤ (q + 1) ^ 3 * ((q + 1) ^ 2 - 1) * ((q + 1) ^ 3 - 1) := by
    have h1 : q ^ 3 ≤ (q + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have h2 : q ^ 2 ≤ (q + 1) ^ 2 - 1 := by
      have : (q + 1) ^ 2 = q ^ 2 + 2 * q + 1 := by ring
      omega
    have h3 : q ^ 3 + 1 ≤ (q + 1) ^ 3 - 1 := by
      have : (q + 1) ^ 3 = q ^ 3 + 3 * q ^ 2 + 3 * q + 1 := by ring
      omega
    exact Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
  exact lt_of_lt_of_le hA hB

private theorem sfm8_su_ne_gl3 {q x : ℕ} (hq : 2 ≤ q) (hx : 2 ≤ x) :
    q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) ≠ x ^ 3 * (x ^ 2 - 1) * (x ^ 3 - 1) := by
  intro h
  rcases le_or_gt x q with hxq | hxq
  · have h1 := sfm8_gl3_mono hxq
    have h2 := sfm8_gl3_lt_su3 hq
    omega
  · have h1 := sfm8_gl3_mono (show q + 1 ≤ x from hxq)
    have h2 := sfm8_su3_lt_gl3_succ hq
    omega

theorem I114FactC_holds : I114FactC := by
  intro K _ _ hZ hcat hdisj
  obtain ⟨k, hk2, hkE, hL⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.I91T.lieModel_of_catalogIs_isL3char2 hcat
  have hord : Nat.card (K ⧸ Subgroup.center K) = CFSG.Open.ordA 2 (2 ^ k) := by
    have := CFSG.GH74.card_of_lieModel_PSL (n := 3) (p := 2) (f := k) (by norm_num) hL
    exact this
  have hx3 : 2 ^ k % 3 = 1 := sfm8_two_pow_mod_three hkE
  have hx2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hN : Nat.card K = (2 ^ k) ^ 3 * ((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 - 1) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center K), hord, hZ]
    have := sfm8_three_mul_ordA hx3
    linarith
  rcases hdisj with hL2 | hH6 | hH7 | hH22 | hSL | hSU
  ·
    obtain ⟨n, hn, hcardL, -⟩ := CFSG.HardMathSupport.Solomon.LocalBalance.Lemma56Ns.sl2_data hL2
    exact ((CFSG.HardMathSupport.Solomon.LocalBalance.Lemma56Ns.arith_two_pow (c := 1) (f := k)
      (n := n) (by norm_num) (by omega) hn).1 (by rw [one_mul, ← hcardL, hN])).elim
  ·
    have hc := CFSG.HardMathSupport.Solomon.LocalBalance.Lemma56Ns.natCard_hatSix hH6
    exact ((CFSG.HardMathSupport.Solomon.LocalBalance.Lemma56Ns.arith_hat (q := 2 ^ k) (c := 1)
      (j := 0) (t := 1080) hx2 (one_dvd _) (by norm_num) (Or.inl rfl)).1
      (by simp only [pow_zero, one_mul]; rw [← hN, hc])).elim
  ·
    have hc := CFSG.HardMathSupport.Solomon.LocalBalance.Lemma56Ns.natCard_hatSeven hH7
    exact ((CFSG.HardMathSupport.Solomon.LocalBalance.Lemma56Ns.arith_hat (q := 2 ^ k) (c := 1)
      (j := 0) (t := 7560) hx2 (one_dvd _) (by norm_num) (Or.inr (Or.inl rfl))).1
      (by simp only [pow_zero, one_mul]; rw [← hN, hc])).elim
  ·
    have hc := CFSG.HardMathSupport.Solomon.LocalBalance.Lemma56Ns.natCard_hatM22 hH22
    exact ((CFSG.HardMathSupport.Solomon.LocalBalance.Lemma56Ns.arith_hat (q := 2 ^ k) (c := 1)
      (j := 0) (t := 1330560) hx2 (one_dvd _) (by norm_num) (Or.inr (Or.inr rfl))).1
      (by simp only [pow_zero, one_mul]; rw [← hN, hc])).elim
  · exact hSL
  ·
    obtain ⟨F, _, _, q, hF, -, ⟨e⟩⟩ := hSU
    have hq2 : 2 ≤ q := CFSG.HardMathSupport.Solomon.LocalBalance.Lemma56Ns.sq_pos_aux hF
      Finite.one_lt_card
    have hKq : Nat.card K = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) := by
      rw [Nat.card_congr e.toEquiv,
        CFSG.HardMathSupport.Solomon.LocalBalance.Lemma56Ns.natCard_statedSU_three hF]
    exact (sfm8_su_ne_gl3 hq2 hx2 (hKq.symm.trans hN)).elim

end CFSG.LocalAnalysis.GLTheoremA.I114
