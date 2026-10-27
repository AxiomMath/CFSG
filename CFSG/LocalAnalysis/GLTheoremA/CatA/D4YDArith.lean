module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4XNArith
public import CFSG.LocalAnalysis.GLTheoremA.S10.CatDistinct

public section

namespace CFSG.LocalAnalysis.GLTheoremA.D4Y

open CFSG.Open

theorem orderD_four_two_pow (e : ℕ) (he : 1 ≤ e) :
    orderD 4 (2 ^ e) = 2 ^ (12 * e) * (((2 ^ e) ^ 4 - 1) * (((2 ^ e) ^ 2 - 1) *
      (((2 ^ e) ^ 4 - 1) * ((2 ^ e) ^ 6 - 1)))) := by
  have hodd : Odd ((2 ^ e) ^ 4 - 1) :=
    CFSG.LocalAnalysis.GLTheoremA.CatDistinct.odd_pow_two_pow_sub_one he (by norm_num)
  have hg : Nat.gcd 4 ((2 ^ e) ^ 4 - 1) = 1 := by
    have h2 : Nat.Coprime 2 ((2 ^ e) ^ 4 - 1) := Nat.coprime_two_left.2 hodd
    have h4 : Nat.Coprime (2 ^ 2) ((2 ^ e) ^ 4 - 1) := Nat.Coprime.pow_left 2 h2
    exact h4
  unfold orderD
  have hI : Finset.Icc 1 (4 - 1) = {1, 2, 3} := by decide
  rw [hI, hg, Nat.div_one]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  have h12 : (2 ^ e) ^ (4 * (4 - 1)) = 2 ^ (12 * e) := by
    rw [← pow_mul]; ring_nf
  rw [h12]
  have a2 : (2 ^ e) ^ (2 * 2) = ((2 ^ e) ^ 4) := by norm_num
  have a3 : (2 ^ e) ^ (2 * 3) = ((2 ^ e) ^ 6) := by norm_num
  have a1 : (2 ^ e) ^ (2 * 1) = ((2 ^ e) ^ 2) := by norm_num
  rw [a1, a2, a3]
  ring

theorem dvd_pow_sub_one {a m : ℕ} (ha : 1 ≤ a) (h : a ≡ 1 [MOD m]) (e : ℕ) : m ∣ a ^ e - 1 := by
  have h1 : a ^ e ≡ 1 [MOD m] := by simpa using h.pow e
  exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ ha)).1 h1.symm

theorem dvd_oddPart (e : ℕ) :
    27 ∣ ((2 ^ e) ^ 4 - 1) * (((2 ^ e) ^ 2 - 1) * (((2 ^ e) ^ 4 - 1) * ((2 ^ e) ^ 6 - 1))) := by
  have h4 : 3 ∣ (2 ^ e) ^ 4 - 1 := by
    have : (2 ^ e) ^ 4 = 16 ^ e := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [this]
    exact dvd_pow_sub_one (by norm_num) (by decide) e
  have h2 : 3 ∣ (2 ^ e) ^ 2 - 1 := by
    have : (2 ^ e) ^ 2 = 4 ^ e := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [this]
    exact dvd_pow_sub_one (by norm_num) (by decide) e
  have h6 : 9 ∣ (2 ^ e) ^ 6 - 1 := by
    have : (2 ^ e) ^ 6 = 64 ^ e := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [this]
    exact dvd_pow_sub_one (by norm_num) (by decide) e
  have := Nat.mul_dvd_mul h4 (Nat.mul_dvd_mul h2 (Nat.mul_dvd_mul h4 h6))
  exact Nat.dvd_trans (by norm_num) this

theorem dvd_orderD (e : ℕ) (he : 1 ≤ e) : 27 ∣ orderD 4 (2 ^ e) := by
  rw [orderD_four_two_pow e he]
  exact Dvd.dvd.mul_left (dvd_oddPart e) _

theorem not_dvd81_A2 (N : ℕ) (hN : 1 ≤ N) (h9 : N % 9 = 4 ∨ N % 9 = 7) :
    ¬ 81 ∣ N ^ 3 * ((N ^ 2 - 1) * (N ^ 3 - 1)) := by
  intro h
  have h1 : 1 ≤ N ^ 2 := Nat.one_le_pow _ _ hN
  have h3 : 1 ≤ N ^ 3 := Nat.one_le_pow _ _ hN
  have h0 : ((N ^ 3 * ((N ^ 2 - 1) * (N ^ 3 - 1)) : ℕ) : ZMod 81) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 h
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub h1, Nat.cast_sub h3] at h0
  push_cast at h0
  have key : ∀ x : ZMod 81, (x.val % 9 = 4 ∨ x.val % 9 = 7) →
      x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 - 1)) ≠ 0 := by decide +kernel
  refine key (N : ZMod 81) ?_ h0
  rw [ZMod.val_natCast]
  omega

theorem not_dvd81_TA2 (N : ℕ) (hN : 1 ≤ N) (h9 : N % 9 = 2 ∨ N % 9 = 5) :
    ¬ 81 ∣ N ^ 3 * ((N ^ 2 - 1) * (N ^ 3 + 1)) := by
  intro h
  have h1 : 1 ≤ N ^ 2 := Nat.one_le_pow _ _ hN
  have h0 : ((N ^ 3 * ((N ^ 2 - 1) * (N ^ 3 + 1)) : ℕ) : ZMod 81) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 h
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub h1] at h0
  push_cast at h0
  have key : ∀ x : ZMod 81, (x.val % 9 = 2 ∨ x.val % 9 = 5) →
      x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 + 1)) ≠ 0 := by decide +kernel
  refine key (N : ZMod 81) ?_ h0
  rw [ZMod.val_natCast]
  omega

theorem not_dvd27_orderA2 (N : ℕ) (h9 : N % 9 = 4 ∨ N % 9 = 7) : ¬ 27 ∣ orderA 2 N := by
  intro h
  have hN : 1 ≤ N := by omega
  rw [CFSG.LocalAnalysis.GLTheoremA.D4XN.orderA_two_eq,
    Nat.gcd_eq_left (show 3 ∣ N - 1 by omega)] at h
  have h3 : 3 ∣ N ^ 3 * ((N ^ 2 - 1) * (N ^ 3 - 1)) := by
    refine Dvd.dvd.mul_left (Dvd.dvd.mul_left ?_ _) _
    have : N ≡ 1 [MOD 3] := by
      rw [Nat.ModEq]; omega
    simpa using dvd_pow_sub_one hN this 3
  obtain ⟨k, hk⟩ := h3
  rw [hk, Nat.mul_div_cancel_left _ (by norm_num)] at h
  apply not_dvd81_A2 N hN h9
  rw [hk]
  obtain ⟨j, rfl⟩ := h
  exact ⟨j, by ring⟩

theorem not_dvd27_orderTA2 (N : ℕ) (h9 : N % 9 = 2 ∨ N % 9 = 5) :
    ¬ 27 ∣ orderTwistedA 2 N := by
  intro h
  have hN : 1 ≤ N := by omega
  rw [CFSG.LocalAnalysis.GLTheoremA.D4XN.orderTwistedA_two_eq,
    Nat.gcd_eq_left (show 3 ∣ N + 1 by omega)] at h
  have h3 : 3 ∣ N ^ 3 * ((N ^ 2 - 1) * (N ^ 3 + 1)) := by
    refine Dvd.dvd.mul_left (Dvd.dvd.mul_left ?_ _) _
    have hm : N % 3 = 2 := by omega
    apply Nat.dvd_of_mod_eq_zero
    simp [Nat.add_mod, Nat.pow_mod, hm]
  obtain ⟨k, hk⟩ := h3
  rw [hk, Nat.mul_div_cancel_left _ (by norm_num)] at h
  apply not_dvd81_TA2 N hN h9
  rw [hk]
  obtain ⟨j, rfl⟩ := h
  exact ⟨j, by ring⟩

theorem orderD_odd_part (e : ℕ) (he : 1 ≤ e) :
    Odd (((2 ^ e) ^ 4 - 1) * (((2 ^ e) ^ 2 - 1) * (((2 ^ e) ^ 4 - 1) * ((2 ^ e) ^ 6 - 1)))) := by
  have h4 := CFSG.LocalAnalysis.GLTheoremA.CatDistinct.odd_pow_two_pow_sub_one (a := e) (j := 4)
    he (by norm_num)
  have h2 := CFSG.LocalAnalysis.GLTheoremA.CatDistinct.odd_pow_two_pow_sub_one (a := e) (j := 2)
    he (by norm_num)
  have h6 := CFSG.LocalAnalysis.GLTheoremA.CatDistinct.odd_pow_two_pow_sub_one (a := e) (j := 6)
    he (by norm_num)
  exact h4.mul (h2.mul (h4.mul h6))

theorem orderA_one_ne_orderD {k e : ℕ} (hk : Odd k) (he : 1 ≤ e) :
    orderA 1 (2 ^ k) ≠ orderD 4 (2 ^ e) := by
  intro h
  have hk1 : 1 ≤ k := hk.pos
  rw [CFSG.LocalAnalysis.GLTheoremA.CatDistinct.orderA_one_eq hk1, orderD_four_two_pow e he] at h
  have hodd : Odd ((2 ^ k) ^ 2 - 1) :=
    CFSG.LocalAnalysis.GLTheoremA.CatDistinct.odd_pow_two_pow_sub_one hk1 (by norm_num)
  obtain ⟨hkk, -⟩ := CFSG.LocalAnalysis.GLTheoremA.CatDistinct.two_pow_mul_odd_inj hodd
    (orderD_odd_part e he) h
  have : Even k := by rw [hkk]; exact ⟨6 * e, by ring⟩
  exact (Nat.not_even_iff_odd.2 hk) this

end CFSG.LocalAnalysis.GLTheoremA.D4Y
