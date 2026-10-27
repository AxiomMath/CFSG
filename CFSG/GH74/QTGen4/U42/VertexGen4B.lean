module

public import CFSG.Quasithin.Background.GoldschmidtListedSolv
public import CFSG.GH74.QTGen4.GL4.NoNine
public import CFSG.GH74.QTGen4.U42.L28Nine
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki.Local

public section

namespace CFSG.GH74.QTGen4.U42.VertexGen4B

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open scoped MatrixGroups

theorem card_GL4_two : Nat.card (GL (Fin 4) (ZMod 2)) = 20160 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.SectionRank.Ccomm.card_GL_zmod 4]
  norm_num [Fin.prod_univ_four]

theorem card_dvd_GL4 {Q : Type} [Group Q] (ψ : Q →* GL (Fin 4) (ZMod 2))
    (hψ : Function.Injective ψ) : Nat.card Q ∣ 20160 := by
  rw [← card_GL4_two]
  exact Subgroup.card_dvd_of_injective ψ hψ

theorem card_psl_galois {n : ℕ} (hn : 1 ≤ n) :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) =
      2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  have hK : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have hodd : ¬ 2 ∣ 2 ^ n - 1 := by
    intro h
    have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    have h3 : 2 ∣ 2 ^ n - (2 ^ n - 1) := Nat.dvd_sub h2 h
    have h4 : 2 ^ n - (2 ^ n - 1) = 1 := by
      have := Nat.one_le_two_pow (n := n)
      omega
    rw [h4] at h3
    omega
  have hgcd : Nat.gcd 2 (2 ^ n - 1) = 1 :=
    Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
  rw [Nat.card_congr (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
      (GaloisField 2 n)).toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num : 1 ≤ 2), hK, hgcd,
    Nat.div_one]
  simp only [Finset.Icc_self, Finset.prod_singleton]
  norm_num

theorem card_sz_formula {a : ℕ} (ha : 1 ≤ a) :
    Nat.card (Sz a) =
      ((2 ^ (2 * a + 1)) ^ 2 + 1) * (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) := by
  rw [Nat.card_congr (CFSG.SignalizerFunctorTheorem.McBride.SzModel.szEquiv a).toEquiv]
  exact CFSG.SectionRank.card_suzukiMatrixGroup a ha

theorem sz_card_gt {q : ℕ} (hq : 8 ≤ q) : 20160 < (q ^ 2 + 1) * q ^ 2 * (q - 1) := by
  have h1 : 64 ≤ q ^ 2 := by nlinarith
  have h2 : 65 ≤ q ^ 2 + 1 := by omega
  have h3 : 7 ≤ q - 1 := by omega
  calc 20160 < 65 * 64 * 7 := by norm_num
    _ ≤ (q ^ 2 + 1) * q ^ 2 * (q - 1) := Nat.mul_le_mul (Nat.mul_le_mul h2 h1) h3

theorem le_toNat_of_le {z : ℤ} {m : ℕ} (h : (m : ℤ) ≤ z) : m ≤ z.toNat := by
  have := Int.self_le_toNat z
  exact_mod_cast le_trans h this

theorem card_statedProj_statedSU_gt {F : Type} [Field F] {n : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = (2 ^ n) ^ 2) :
    20160 < Nat.card (CFSG.Assembly.LowTwoRank.StatedProj
      (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ n) F)) := by
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two (by omega) hF
    (by norm_num : (2 : ℕ) ≤ 3)]
  have hq4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  rw [show (3 : ℕ) * (3 - 1) / 2 = 3 from rfl,
    show Finset.Icc 2 3 = ({2, 3} : Finset ℕ) from by decide, Finset.prod_pair (by norm_num)]
  generalize 2 ^ n = q at hq4 ⊢
  have hq4' : (4 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq4
  have hq2N : 16 ≤ q ^ 2 := by nlinarith
  have hq3N : 64 ≤ q ^ 3 := by nlinarith
  have hq2 : (16 : ℤ) ≤ (q : ℤ) ^ 2 := by exact_mod_cast hq2N
  have hq3 : (64 : ℤ) ≤ (q : ℤ) ^ 3 := by exact_mod_cast hq3N
  have hA : 15 ≤ ((q : ℤ) ^ 2 - (-1) ^ 2).toNat :=
    le_toNat_of_le (by push_cast; nlinarith)
  have hB : 65 ≤ ((q : ℤ) ^ 3 - (-1) ^ 3).toNat :=
    le_toNat_of_le (by push_cast; nlinarith)
  generalize ((q : ℤ) ^ 2 - (-1) ^ 2).toNat = A at hA ⊢
  generalize ((q : ℤ) ^ 3 - (-1) ^ 3).toNat = B at hB ⊢
  have hg : Nat.gcd 3 (q + 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
  have hgpos : 0 < Nat.gcd 3 (q + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hX : 62400 ≤ q ^ 3 * (A * B) := by
    have h64 : 64 ≤ q ^ 3 := hq3N
    calc 62400 = 64 * (15 * 65) := by norm_num
      _ ≤ q ^ 3 * (A * B) := Nat.mul_le_mul h64 (Nat.mul_le_mul hA hB)
  have h2 : 20161 ≤ q ^ 3 * (A * B) / Nat.gcd 3 (q + 1) := by
    rw [Nat.le_div_iff_mul_le hgpos]
    nlinarith [hX, hg]
  exact lt_of_lt_of_le (by norm_num) h2

theorem card_statedSU_gt {F : Type} [Field F] {n : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = (2 ^ n) ^ 2)
    (hfin : Finite (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ n) F)) :
    20160 < Nat.card (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ n) F) := by
  haveI := hfin
  refine lt_of_lt_of_le (card_statedProj_statedSU_gt hn hF) ?_
  exact Nat.card_le_card_of_surjective
    (QuotientGroup.mk' ((CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) F).subgroupOf
      (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ n) F)))
    (QuotientGroup.mk'_surjective _)

theorem listed_case_two {Q : Type} [Group Q] [Finite Q]
    (hQ : CFSG.Quasithin.IsRankOneListed Q) (hns : ¬ Group.IsSolvable Q)
    (ψ : Q →* GL (Fin 4) (ZMod 2)) (hψ : Function.Injective ψ) :
    CFSG.Quasithin.IsL2Quot 2 Q := by
  have hdvd := card_dvd_GL4 ψ hψ
  rcases hQ with ⟨n, hn, ⟨e⟩⟩ | ⟨a, ⟨e⟩⟩ | ⟨n, hn, F, i1, i2, hF, ⟨e⟩⟩ |
    ⟨n, hn, F, i1, i2, hF, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  ·
    rcases Nat.lt_or_ge n 2 with h1 | h2
    · obtain rfl : n = 1 := by omega
      exact absurd (CFSG.Quasithin.IsSmallListed.isSolvable
        (Or.inl (CFSG.Quasithin.isL2Quot_one_iff_perm3.1 ⟨e⟩))) hns
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · obtain rfl : n = 2 := by omega
      exact ⟨e⟩
    rcases Nat.lt_or_ge n 4 with h4 | h4
    · obtain rfl : n = 3 := by omega
      obtain ⟨x, hx⟩ := CFSG.GH74.QTGen4.U42.L28Nine.isL2Quot_three_exists_orderOf_nine ⟨e⟩
      exact (CFSG.GH74.QTGen4.orderOf_ne_nine_of_injective ψ hψ x hx).elim
    have hcard : Nat.card Q = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv, card_psl_galois (by omega)]
    rw [hcard] at hdvd
    rcases Nat.lt_or_ge n 5 with h5 | h5
    · obtain rfl : n = 4 := by omega
      norm_num at hdvd
    · have hq : 32 ≤ 2 ^ n := by
        calc (32 : ℕ) = 2 ^ 5 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h5
      have hle := Nat.le_of_dvd (by norm_num) hdvd
      have hq2 : 32 ^ 2 ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left hq 2
      have hbig : 32 * (32 ^ 2 - 1) ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) :=
        Nat.mul_le_mul hq (Nat.sub_le_sub_right hq2 1)
      have key : 20160 < 2 ^ n * ((2 ^ n) ^ 2 - 1) := lt_of_lt_of_le (by norm_num) hbig
      exact absurd hle (not_le.mpr key)
  ·
    rcases Nat.eq_zero_or_pos a with h0 | h1
    · subst h0
      exact absurd (CFSG.Quasithin.IsSmallListed.isSolvable
        (Or.inr (Or.inl (Or.inr ⟨e⟩)))) hns
    · have hq : 8 ≤ 2 ^ (2 * a + 1) := by
        calc (8 : ℕ) = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hcard : Nat.card Q = ((2 ^ (2 * a + 1)) ^ 2 + 1) * (2 ^ (2 * a + 1)) ^ 2 *
          (2 ^ (2 * a + 1) - 1) := by
        rw [Nat.card_congr e.toEquiv, card_sz_formula h1]
      rw [hcard] at hdvd
      have hle := Nat.le_of_dvd (by norm_num) hdvd
      exact absurd hle (not_le.mpr (sz_card_gt hq))
  ·
    rcases Nat.lt_or_ge n 2 with h1 | h2
    · obtain rfl : n = 1 := by omega
      exact absurd (CFSG.Quasithin.IsSmallListed.isSolvable
        (Or.inr (Or.inr ⟨F, i1, i2, by simpa using hF, Or.inl ⟨e⟩⟩))) hns
    · have hfin : Finite (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ n) F) :=
        Finite.of_equiv Q e.toEquiv
      have hcard : Nat.card Q = Nat.card (StatedSU 3 (2 ^ n) F) :=
        Nat.card_congr e.toEquiv
      rw [hcard] at hdvd
      have hle := Nat.le_of_dvd (by norm_num) hdvd
      exact absurd hle (not_le.mpr (card_statedSU_gt h2 hF hfin))
  ·
    rcases Nat.lt_or_ge n 2 with h1 | h2
    · obtain rfl : n = 1 := by omega
      exact absurd (CFSG.Quasithin.IsSmallListed.isSolvable
        (Or.inr (Or.inr ⟨F, i1, i2, by simpa using hF, Or.inr ⟨e⟩⟩))) hns
    · have hcard : Nat.card Q =
          Nat.card (CFSG.Assembly.LowTwoRank.StatedProj
            (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ n) F)) :=
        Nat.card_congr e.toEquiv
      rw [hcard] at hdvd
      have hle := Nat.le_of_dvd (by norm_num) hdvd
      exact absurd hle (not_le.mpr (card_statedProj_statedSU_gt h2 hF))
  ·
    exact absurd (CFSG.Quasithin.IsSmallListed.isSolvable
      (Or.inr (Or.inl (Or.inl ⟨e⟩)))) hns

end CFSG.GH74.QTGen4.U42.VertexGen4B
