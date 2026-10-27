module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21Defs
public import CFSG.Adapters.StatedClassicalOrders
public import CFSG.Adapters.StatedClassicalUnitaryOrders
public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.M11Order
public import CFSG.Walter.J1Props.Elt
public import CFSG.Open.Defs
public import CFSG.Open.StatedDefs
public import CFSG.Open.WalterAbelianSylowTwoMilestoneDefs
public import Certificates.Certificate110
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.LinearAlgebra.Matrix.CharP
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.EvenBN.Tits.Prelim.SecTwoConstrained
public import CFSG.LocalAnalysis.EvenBN.Tits.Prelim.SecTwoQuotient

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21.Filter

open Subgroup CFSG.Open
open scoped MatrixGroups

section Arith

theorem factorization_two_eq {n k : ℕ} (hn : n ≠ 0) (h1 : 2 ^ k ∣ n) (h2 : ¬ 2 ^ (k + 1) ∣ n) :
    n.factorization 2 = k := by
  have a := (Nat.prime_two.pow_dvd_iff_le_factorization hn).mp h1
  have b : ¬ k + 1 ≤ n.factorization 2 := fun hb =>
    h2 ((Nat.prime_two.pow_dvd_iff_le_factorization hn).mpr hb)
  omega

theorem prime_pow_dvd_N {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (hd : p ^ n ∣ sec622N) :
    (p = 2 ∧ n ≤ 28) ∨ (p = 3 ∧ n ≤ 5) ∨ (p = 5 ∧ n ≤ 2) ∨ (p = 7 ∧ n ≤ 2) ∨
      (p = 17 ∧ n = 1) ∨ (p = 31 ∧ n = 1) ∨ (p = 127 ∧ n = 1) := by
  have hpd : p ∣ 2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127 :=
    (dvd_pow_self p (by omega)).trans hd
  have hle : ∀ m : ℕ, ¬ p ^ (m + 1) ∣ sec622N → n ≤ m := fun m hm => by
    by_contra h
    exact hm ((pow_dvd_pow p (by omega)).trans hd)
  simp only [hp.dvd_mul] at hpd
  rcases hpd with (((((h | h) | h) | h) | h) | h) | h
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
    exact Or.inl ⟨rfl, hle 28 (by decide +kernel)⟩
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h)
    exact Or.inr (Or.inl ⟨rfl, hle 5 (by decide +kernel)⟩)
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp (hp.dvd_of_dvd_pow h)
    exact Or.inr (Or.inr (Or.inl ⟨rfl, hle 2 (by decide +kernel)⟩))
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7)).mp
      (hp.dvd_of_dvd_pow h)
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hle 2 (by decide +kernel)⟩)))
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 17)).mp h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨rfl, by have := hle 1 (by decide +kernel); omega⟩))))
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 31)).mp h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨rfl, by have := hle 1 (by decide +kernel); omega⟩)))))
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 127)).mp h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨rfl, by have := hle 1 (by decide +kernel); omega⟩)))))

end Arith

section PSLTwo

theorem card_psl_two (F : Type) [Field F] [Finite F] :
    Nat.card (PSL(2, F)) = Nat.card F * (Nat.card F ^ 2 - 1) / Nat.gcd 2 (Nat.card F - 1) := by
  rw [CFSG.OrderReductions.LinearOrders.card_projectiveSpecialLinear F 2 (by norm_num)]
  simp

theorem card_psl_two_odd (F : Type) [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    Nat.card (PSL(2, F)) = Nat.card F * (Nat.card F ^ 2 - 1) / 2 := by
  rw [card_psl_two]
  congr 1
  apply Nat.gcd_eq_left
  obtain ⟨k, hk⟩ := hodd
  exact ⟨k, by omega⟩

theorem card_psl_two_even (F : Type) [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hq : Nat.card F = 2 ^ n) :
    Nat.card (PSL(2, F)) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  rw [card_psl_two]
  have hodd : Odd (Nat.card F - 1) := by
    rw [hq]
    exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  rw [(Nat.coprime_two_left.mpr hodd).gcd_eq_one, Nat.div_one]

theorem card_eq_prime_pow (F : Type) [Field F] [Finite F] (p : ℕ) [CharP F p] :
    ∃ n : ℕ, 1 ≤ n ∧ p.Prime ∧ Nat.card F = p ^ n := by
  haveI := Fintype.ofFinite F
  obtain ⟨n, hp, hn⟩ := FiniteField.card F p
  exact ⟨n, n.pos, hp, by rw [Nat.card_eq_fintype_card]; exact hn⟩

theorem filter_psl_odd_arith {q p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (hq : q = p ^ n)
    (hodd : Odd q) (h5 : 5 ≤ q) (hd : q * (q ^ 2 - 1) / 2 ∣ sec622N) :
    (q = 5 ∧ (q * (q ^ 2 - 1) / 2).factorization 2 = 2) ∨
    (q = 7 ∧ (q * (q ^ 2 - 1) / 2).factorization 2 = 3) ∨
    (q = 9 ∧ (q * (q ^ 2 - 1) / 2).factorization 2 = 3) ∨
    (q = 17 ∧ (q * (q ^ 2 - 1) / 2).factorization 2 = 4) ∨
    (q = 31 ∧ (q * (q ^ 2 - 1) / 2).factorization 2 = 5) ∨
    (q = 49 ∧ (q * (q ^ 2 - 1) / 2).factorization 2 = 4) ∨
    (q = 127 ∧ (q * (q ^ 2 - 1) / 2).factorization 2 = 7) := by
  have h2 : 2 ∣ q ^ 2 - 1 :=
    even_iff_two_dvd.mp (Nat.Odd.sub_odd (hodd.pow) odd_one)
  have hqd : q ∣ q * (q ^ 2 - 1) / 2 := by
    rw [Nat.mul_div_assoc q h2]
    exact Dvd.intro _ rfl
  have hpn : p ^ n ∣ sec622N := hq ▸ hqd.trans hd
  subst hq
  rcases prime_pow_dvd_N hp hn hpn with ⟨rfl, hn'⟩ | ⟨rfl, hn'⟩ | ⟨rfl, hn'⟩ | ⟨rfl, hn'⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exfalso
    exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  all_goals
    (try interval_cases n) <;> first
      | exact absurd hd (by decide +kernel)
      | (exfalso; revert h5; norm_num; done)
      | exact Or.inl ⟨rfl, factorization_two_eq (by norm_num) (by norm_num) (by norm_num)⟩
      | exact Or.inr (Or.inl ⟨rfl, factorization_two_eq (by norm_num) (by norm_num)
          (by norm_num)⟩)
      | exact Or.inr (Or.inr (Or.inl ⟨rfl, factorization_two_eq (by norm_num) (by norm_num)
          (by norm_num)⟩))
      | exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, factorization_two_eq (by norm_num)
          (by norm_num) (by norm_num)⟩)))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, factorization_two_eq (by norm_num)
          (by norm_num) (by norm_num)⟩))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, factorization_two_eq
          (by norm_num) (by norm_num) (by norm_num)⟩)))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, factorization_two_eq
          (by norm_num) (by norm_num) (by norm_num)⟩)))))

end PSLTwo

section Rank3

theorem q_cube_dvd_psl_three (q : ℕ) :
    q ^ 3 ∣ (q ^ (3 * (3 - 1) / 2) * ∏ i ∈ Finset.Icc 2 3, (q ^ i - 1)) / Nat.gcd 3 (q - 1) := by
  have hgP : Nat.gcd 3 (q - 1) ∣ ∏ i ∈ Finset.Icc 2 3, (q ^ i - 1) :=
    (Nat.gcd_dvd_right 3 (q - 1)).trans
      ((Nat.sub_one_dvd_pow_sub_one q 2).trans
        (Finset.dvd_prod_of_mem (fun i => q ^ i - 1) (by simp)))
  rw [show 3 * (3 - 1) / 2 = 3 by norm_num, Nat.mul_div_assoc _ hgP]
  exact Dvd.intro _ rfl

theorem q_cube_dvd_psu_three (q : ℕ) :
    q ^ 3 ∣ q ^ (3 * (3 - 1) / 2) *
      (∏ i ∈ Finset.Icc 2 3, (((q : ℕ) : ℤ) ^ i - (-1) ^ i).toNat) / Nat.gcd 3 (q + 1) := by
  have h3 : (((q : ℕ) : ℤ) ^ 3 - (-1) ^ 3).toNat = q ^ 3 + 1 := by
    have : ((q : ℕ) : ℤ) ^ 3 - (-1) ^ 3 = ((q ^ 3 + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [this, Int.toNat_natCast]
  have hq1 : q + 1 ∣ q ^ 3 + 1 := by
    simpa using Odd.nat_add_dvd_pow_add_pow q 1 (by decide : Odd 3)
  have hgP : Nat.gcd 3 (q + 1) ∣
      ∏ i ∈ Finset.Icc 2 3, (((q : ℕ) : ℤ) ^ i - (-1) ^ i).toNat := by
    refine (Nat.gcd_dvd_right 3 (q + 1)).trans (hq1.trans ?_)
    rw [← h3]
    exact Finset.dvd_prod_of_mem (fun i => (((q : ℕ) : ℤ) ^ i - (-1) ^ i).toNat)
      (by simp : 3 ∈ Finset.Icc 2 3)
  rw [show 3 * (3 - 1) / 2 = 3 by norm_num, Nat.mul_div_assoc _ hgP]
  exact Dvd.intro _ rfl

theorem prime_pow_three {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hodd : p ≠ 2)
    (hd : (p ^ f) ^ 3 ∣ sec622N) : p = 3 ∧ f = 1 := by
  rw [← pow_mul] at hd
  rcases prime_pow_dvd_N hp (by omega) hd with ⟨h2, -⟩ | ⟨h3, hn⟩ | ⟨h5, hn⟩ | ⟨h7, hn⟩ |
    ⟨h17, hn⟩ | ⟨h31, hn⟩ | ⟨h127, hn⟩
  · exact absurd h2 hodd
  · exact ⟨h3, by omega⟩
  all_goals omega

end Rank3

section EvenFour

theorem fin_two_sq {F : Type} [Field F] (N : Matrix (Fin 2) (Fin 2) F) :
    N ^ 2 = N.trace • N - N.det • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sq, Matrix.mul_apply, Matrix.trace_fin_two, Matrix.det_fin_two] <;>
    ring

theorem mat_sq_eq_one {F : Type} [Field F] [CharP F 2] (M : Matrix (Fin 2) (Fin 2) F)
    (h4 : M ^ 4 = 1) : M ^ 2 = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (2 : Matrix (Fin 2) (Fin 2) F) = 0 := by
    simpa using CharP.cast_eq_zero (Matrix (Fin 2) (Fin 2) F) 2
  have hN4 : (M + 1) ^ 4 = 0 := by
    have := add_pow_char_pow_of_commute (p := 2) (n := 2) (Commute.one_right M)
    simp only [show (2 : ℕ) ^ 2 = 4 by norm_num, one_pow, h4] at this
    rw [this, one_add_one_eq_two, h2]
  have hdN : (M + 1).det = 0 := by
    have := congrArg Matrix.det hN4
    rw [Matrix.det_pow, Matrix.det_zero] at this
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  have hCH := fin_two_sq (M + 1)
  rw [hdN, zero_smul, sub_zero] at hCH
  have hpow : ∀ k : ℕ, (M + 1) ^ (k + 1) = (M + 1).trace ^ k • (M + 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ih, smul_mul_assoc, ← sq, hCH, smul_smul, ← pow_succ]
  have hN2 : (M + 1) ^ 2 = 0 := by
    have h3 := hpow 3
    rw [hN4] at h3
    rcases smul_eq_zero.mp h3.symm with ht | hz
    · rw [hCH, pow_eq_zero_iff (by norm_num) |>.mp ht, zero_smul]
    · rw [hz]
      simp
  have hsum : M ^ 2 + 1 = 0 := by
    have := add_pow_char_of_commute (p := 2) (Commute.one_right M)
    rw [one_pow] at this
    rw [← this]
    exact hN2
  calc M ^ 2 = (M ^ 2 + 1) + 1 := by rw [add_assoc, one_add_one_eq_two, h2, add_zero]
    _ = 1 := by rw [hsum, zero_add]

end EvenFour

end CFSG.LocalAnalysis.EvenBN.Tits.I21.Filter

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Open
open scoped MatrixGroups

theorem sec622_filter_psl_odd {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (h5 : 5 ≤ Nat.card F) (hdvd : Nat.card (PSL(2, F)) ∣ sec622N) :
    (Nat.card F = 5 ∧ (Nat.card (PSL(2, F))).factorization 2 = 2) ∨
    (Nat.card F = 7 ∧ (Nat.card (PSL(2, F))).factorization 2 = 3) ∨
    (Nat.card F = 9 ∧ (Nat.card (PSL(2, F))).factorization 2 = 3) ∨
    (Nat.card F = 17 ∧ (Nat.card (PSL(2, F))).factorization 2 = 4) ∨
    (Nat.card F = 31 ∧ (Nat.card (PSL(2, F))).factorization 2 = 5) ∨
    (Nat.card F = 49 ∧ (Nat.card (PSL(2, F))).factorization 2 = 4) ∨
    (Nat.card F = 127 ∧ (Nat.card (PSL(2, F))).factorization 2 = 7) := by
  haveI := ringChar.charP F
  obtain ⟨n, hn, hp, hq⟩ := I21.Filter.card_eq_prime_pow F (ringChar F)
  rw [I21.Filter.card_psl_two_odd F hodd] at hdvd ⊢
  exact I21.Filter.filter_psl_odd_arith hp hn hq hodd h5 hdvd

theorem sec622_psl2_even_no_order_four {F : Type} [Field F] [Finite F] (hchar : ringChar F = 2)
    (g : PSL(2, F)) (hg : g ^ 4 = 1) : g ^ 2 = 1 := by
  haveI : CharP F 2 := ringChar.of_eq hchar
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective g
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hg
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
  have hr1 : r = 1 := by
    have h2 : r ^ 2 = 1 := by simpa using hr
    have h0 : (r + 1) ^ 2 = 0 := by
      rw [CharTwo.add_sq, h2, one_pow, CharTwo.add_self_eq_zero]
    have := eq_neg_of_add_eq_zero_left (pow_eq_zero_iff (two_ne_zero) |>.mp h0)
    rw [this, CharTwo.neg_eq]
  have hA4 : (A : Matrix (Fin 2) (Fin 2) F) ^ 4 = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, ← hrA, hr1, map_one]
  have hA2 : A ^ 2 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow]
    exact I21.Filter.mat_sq_eq_one (A : Matrix (Fin 2) (Fin 2) F) hA4
  rw [hA2]
  exact one_mem _

theorem sec622_not_psl_three {L : Type} [Group L] {p f : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hm : StatedClassicalModel L .PSL 3 p f) (hdvd : Nat.card L ∣ sec622N) : False := by
  obtain ⟨-, hf, -⟩ := hm.1
  rw [StatedAPI.card_of_statedClassicalModel_psl (by norm_num) hm] at hdvd
  obtain ⟨rfl, rfl⟩ := I21.Filter.prime_pow_three hp hf hodd
    ((I21.Filter.q_cube_dvd_psl_three (p ^ f)).trans hdvd)
  exact absurd hdvd (by decide +kernel)

theorem sec622_psu_three {L : Type} [Group L] {p f : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hm : StatedClassicalModel L .PSU 3 p f) (hdvd : Nat.card L ∣ sec622N) : p ^ f = 3 := by
  obtain ⟨-, hf, -⟩ := hm.1
  rw [StatedAPI.card_of_statedClassicalModel_psu (by norm_num) hm] at hdvd
  obtain ⟨rfl, rfl⟩ := I21.Filter.prime_pow_three hp hf hodd
    ((I21.Filter.q_cube_dvd_psu_three (p ^ f)).trans hdvd)
  rfl

theorem sec622_not_M11 {L : Type} [Group L] (e : L ≃* StatedM11)
    (hdvd : Nat.card L ∣ sec622N) : False := by
  rw [Nat.card_congr e.toEquiv, CFSG.Semidihedral.GL2Recognition.card_statedM11] at hdvd
  exact absurd hdvd (by decide +kernel)

theorem sec622_not_J1 {L : Type} [Group L] (e : L ≃* walterJ1) (hdvd : Nat.card L ∣ sec622N) :
    False := by
  rw [Nat.card_congr e.toEquiv, CFSG.Walter.J1Props.card_walterJ1] at hdvd
  exact absurd hdvd (by decide +kernel)

theorem sec622_not_ree {m : ℕ} (hm : 1 ≤ m) (hdvd : ordRee (3 ^ (2 * m + 1)) ∣ sec622N) :
    False := by
  have h1 : (3 ^ (2 * m + 1)) ^ 3 ∣ ordRee (3 ^ (2 * m + 1)) :=
    ((Dvd.intro _ rfl : (3 ^ (2 * m + 1)) ^ 3 ∣
      (3 ^ (2 * m + 1)) ^ 3 * ((3 ^ (2 * m + 1)) ^ 3 + 1)).mul_right _)
  have h2 : 3 ^ 9 ∣ (3 ^ (2 * m + 1)) ^ 3 := by
    rw [← pow_mul]
    exact pow_dvd_pow 3 (by omega)
  exact (by decide +kernel : ¬ 3 ^ 9 ∣ sec622N) (h2.trans (h1.trans hdvd))

end CFSG.LocalAnalysis.EvenBN.Tits
