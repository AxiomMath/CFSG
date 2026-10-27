module

public import CFSG.GH74.GLS.Stage2.Final.ClassicalN
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93ModelJ
public import CFSG.LocalAnalysis.OddStandard.Solomon75T11bArith

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem false_of_card_eq_of_factorization {N m : ℕ} (hv : N.factorization 2 = 8) (hN : N = m)
    (hm : ¬ 2 ^ 8 ∣ m) : False := by
  apply hm
  have := Nat.ordProj_dvd N 2
  rw [hv, hN] at this
  exact this

theorem two_pow_mod_four_ne_one {f : ℕ} (hf : 1 ≤ f) : 2 ^ f % 4 ≠ 1 := by
  rcases Nat.lt_or_ge f 2 with h | h
  · obtain rfl : f = 1 := by omega
    norm_num
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [pow_add]
    simp

theorem three_pow_mod_eight (k : ℕ) : 3 ^ (2 * k + 1) % 8 = 3 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have : 3 ^ (2 * (k + 1) + 1) = 3 ^ (2 * k + 1) * 9 := by ring
    rw [this, Nat.mul_mod, ih]

theorem natCast_pow_toNat (q i : ℕ) : ((q : ℤ) ^ i).toNat = q ^ i := by
  rw [← Nat.cast_pow, Int.toNat_natCast]

theorem natCast_pow_add_one_toNat (q i : ℕ) : ((q : ℤ) ^ i + 1).toNat = q ^ i + 1 := by
  have : ((q : ℤ) ^ i + 1) = ((q ^ i + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [this, Int.toNat_natCast]

theorem not_eight_of_lieModel_PSL4 {G : Type} [Group G] {p f : ℕ}
    (hmod : p ^ f % 8 ≠ 1) (hq : (p ^ f) % 2 = 1) (h : LieModel G .PSL 4 p f) :
    (Nat.card G).factorization 2 ≠ 8 := by
  have hcard := CFSG.GH74.card_of_lieModel_PSL (n := 4) (by norm_num) h
  generalize p ^ f = q at hcard hmod hq
  have hdvd : Nat.gcd 4 (q - 1) ∣ q ^ (3 * (3 + 1) / 2) *
      ∏ i ∈ Finset.Icc 2 (3 + 1), (q ^ i - 1) := by
    have h1 : Nat.gcd 4 (q - 1) ∣ q - 1 := Nat.gcd_dvd_right _ _
    have h2 : q - 1 ∣ q ^ 2 - 1 := by simpa using Nat.sub_dvd_pow_sub_pow q 1 2
    have h3 : q ^ 2 - 1 ∣ ∏ i ∈ Finset.Icc 2 (3 + 1), (q ^ i - 1) :=
      Finset.dvd_prod_of_mem (fun i => q ^ i - 1) (by simp : (2 : ℕ) ∈ Finset.Icc 2 (3 + 1))
    exact (h1.trans (h2.trans h3)).mul_left _
  have hN : Nat.card G * Nat.gcd 4 (q - 1) = mPSL4 q := by
    rw [hcard]
    unfold CFSG.Open.ordA
    rw [Nat.sub_add_cancel (by norm_num : 1 ≤ 4)] at *
    rw [Nat.div_mul_cancel (by simpa using hdvd)]
    unfold mPSL4
    simp [Finset.prod_Icc_succ_top, mul_assoc]
  exact not_eight_PSL4 hq hmod hN

theorem not_eight_of_lieModel_PSU4 {G : Type} [Group G] {p f : ℕ} (hp2 : p ≠ 2)
    (hmod : p ^ f % 8 ≠ 7) (hq3 : 3 ≤ p ^ f) (hq : (p ^ f) % 2 = 1) (h : LieModel G .PSU 4 p f) :
    (Nat.card G).factorization 2 ≠ 8 := by
  have hcard := CFSG.GH74.card_of_lieModel_PSU (n := 4) (by norm_num) hp2 h
  generalize p ^ f = q at hcard hmod hq3 hq
  unfold CFSG.Open.ordTwistedA at hcard
  simp [Finset.prod_Icc_succ_top, mul_assoc] at hcard
  simp only [natCast_pow_toNat, natCast_pow_add_one_toNat] at hcard
  have hdvd : Nat.gcd 4 (q + 1) ∣ q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 + 1) * (q ^ 4 - 1))) := by
    have h1 : Nat.gcd 4 (q + 1) ∣ q + 1 := Nat.gcd_dvd_right _ _
    have h2 : q + 1 ∣ q ^ 3 + 1 := by
      simpa using Odd.nat_add_dvd_pow_add_pow q 1 (by decide : Odd 3)
    exact (((h1.trans h2).mul_right _).mul_left _).mul_left _
  have hN : Nat.card G * Nat.gcd 4 (q + 1) = mPSU4 q := by
    rw [hcard, Nat.div_mul_cancel hdvd]
    rfl
  exact not_eight_PSU4 hq hmod hq3 hN

theorem not_eight_of_lieModel_PSL5 {G : Type} [Group G] {p f : ℕ}
    (hmod : p ^ f % 4 = 3) (h : LieModel G .PSL 5 p f) :
    (Nat.card G).factorization 2 ≠ 8 := by
  have hcard := CFSG.GH74.card_of_lieModel_PSL (n := 5) (by norm_num) h
  generalize p ^ f = q at hcard hmod
  unfold CFSG.Open.ordA at hcard
  simp [Finset.prod_Icc_succ_top, mul_assoc] at hcard
  have hdvd : Nat.gcd 5 (q - 1) ∣
      q ^ 10 * ((q ^ 2 - 1) * ((q ^ 3 - 1) * ((q ^ 4 - 1) * (q ^ 5 - 1)))) := by
    have h1 : Nat.gcd 5 (q - 1) ∣ q - 1 := Nat.gcd_dvd_right _ _
    have h2 : q - 1 ∣ q ^ 2 - 1 := by simpa using Nat.sub_dvd_pow_sub_pow q 1 2
    exact (((h1.trans h2).mul_right _).mul_left _)
  have hN : Nat.card G * Nat.gcd 5 (q - 1) = mPSL5 q := by
    rw [hcard, Nat.div_mul_cancel hdvd]
    rfl
  exact not_eight_PSL5 hmod hN

theorem not_eight_of_lieModel_PSU5 {G : Type} [Group G] {p f : ℕ} (hp2 : p ≠ 2)
    (hmod : p ^ f % 4 = 1) (hq3 : 3 ≤ p ^ f) (h : LieModel G .PSU 5 p f) :
    (Nat.card G).factorization 2 ≠ 8 := by
  have hcard := CFSG.GH74.card_of_lieModel_PSU (n := 5) (by norm_num) hp2 h
  generalize p ^ f = q at hcard hmod hq3
  unfold CFSG.Open.ordTwistedA at hcard
  simp [Finset.prod_Icc_succ_top, mul_assoc] at hcard
  simp only [natCast_pow_toNat, natCast_pow_add_one_toNat] at hcard
  have hdvd : Nat.gcd 5 (q + 1) ∣
      q ^ 10 * ((q ^ 2 - 1) * ((q ^ 3 + 1) * ((q ^ 4 - 1) * (q ^ 5 + 1)))) := by
    have h1 : Nat.gcd 5 (q + 1) ∣ q + 1 := Nat.gcd_dvd_right _ _
    have h2 : q + 1 ∣ q ^ 3 + 1 := by
      simpa using Odd.nat_add_dvd_pow_add_pow q 1 (by decide : Odd 3)
    exact (((h1.trans h2).mul_right _).mul_left _).mul_left _
  have hN : Nat.card G * Nat.gcd 5 (q + 1) = mPSU5 q := by
    rw [hcard, Nat.div_mul_cancel hdvd]
    rfl
  exact not_eight_PSU5 hmod hq3 hN

section Ree


theorem not_eight_of_lieModel_twistedG2 {G : Type} [Group G] {f : ℕ}
    (h : LieModel G .twistedG2 0 3 f) : (Nat.card G).factorization 2 ≠ 8 := by
  obtain ⟨k, -, hcard⟩ := CFSG.GH74.card_of_lieModel_twistedG2 h
  have hq := three_pow_mod_eight k
  generalize 3 ^ (2 * k + 1) = q at hcard hq
  have hN : Nat.card G * 1 = mRee q := by
    rw [hcard, mul_one]
    simp [CFSG.Open.ordRee, mRee, mul_assoc]
  exact not_eight_Ree hq hN

end Ree

theorem false_of_psp4_oneClass {G : Type} [Group G] [Finite G] {t : G} (ht : orderOf t = 2)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hm : LieModel G .PSp 2 p f)
    (P : Sylow 2 G) (htP : t ∈ (P : Subgroup G)) (htc : ∀ x ∈ (P : Subgroup G), x * t = t * x)
    (hone : ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v) : False := by
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hK : GH74.GLS.IVK.IsSp4L4U4 G (p ^ f) :=
    Or.inl (GH74.GLS.Stage2.Final.isPSp4_of_lieModel hm)
  obtain ⟨y, b, hy, hnc, -⟩ :=
    GH74.GLS.IVK.Proofs2.Ivk93Adapt.jm_card_classes hodd hq hK P htP ht htc
  exact hnc (hone t y ht hy)

end CFSG.OddStandard.Solomon75
