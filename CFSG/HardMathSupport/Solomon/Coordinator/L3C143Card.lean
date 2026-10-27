module

public import CFSG.Quasithin.Vol2.Ch5Sec1Thm5114SL3
public import CFSG.Quasithin.Background.GoldschmidtListedSolv
public import CFSG.Timmesfeld.Orders.ClassicalLinear
import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThreeSU
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec2Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance

theorem card_psu_three_eight {K : Type} [Field K] (hK : Nat.card K = 8 ^ 2) :
    Nat.card (StatedProj (StatedSU 3 8 K)) = 5515776 := by
  have h : Nat.card (StatedProj (StatedSU 3 (2 ^ 3) K)) =
      (2 ^ 3) ^ (3 * (3 - 1) / 2) *
        (∏ i ∈ Finset.Icc 2 3, ((((2 ^ 3 : ℕ) : ℕ) : ℤ) ^ i - (-1) ^ i).toNat) /
          Nat.gcd 3 (2 ^ 3 + 1) :=
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (K := K) (p := 2) (f := 3)
      (n := 3) Nat.prime_two (by norm_num) (by rw [hK]; norm_num) (by norm_num)
  rw [show (2 : ℕ) ^ 3 = 8 by norm_num] at h
  rw [h, show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)]
  norm_num

theorem card_statedSU_three_of' {K : Type} [Field K] [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2) :
    Nat.card ↥(StatedSU 3 q K) = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) :=
  CFSG.SectionRank.OddCover.card_statedSU_three_of_card_eq_sq hK

theorem le_of_cube_dvd {r k : ℕ} (hr3 : r % 3 ≠ 0) (hd : r ^ 3 ∣ 3 ^ k * 5515776) :
    r ^ 3 ∣ 5515776 := by
  have hc : Nat.Coprime (r ^ 3) (3 ^ k) :=
    Nat.Coprime.pow _ _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega)).symm
  exact hc.dvd_of_dvd_mul_left hd

theorem eq_four_of_cube_dvd {r : ℕ} (h9 : r % 9 = 4 ∨ r % 9 = 7) (hd : r ^ 3 ∣ 5515776)
    (hpos : 2 ≤ r) : r = 4 := by
  have hle : r ^ 3 ≤ 5515776 := Nat.le_of_dvd (by norm_num) hd
  have hr : r < 177 := by
    by_contra hc
    push Not at hc
    have : 177 ^ 3 ≤ r ^ 3 := Nat.pow_le_pow_left hc 3
    omega
  interval_cases r <;> omega

theorem eq_two_of_cube_dvd {r : ℕ} (h9 : r % 9 = 2 ∨ r % 9 = 5) (hd : r ^ 3 ∣ 5515776)
    (hpos : 2 ≤ r) : r = 2 := by
  have hle : r ^ 3 ≤ 5515776 := Nat.le_of_dvd (by norm_num) hd
  have hr : r < 177 := by
    by_contra hc
    push Not at hc
    have : 177 ^ 3 ≤ r ^ 3 := Nat.pow_le_pow_left hc 3
    omega
  interval_cases r <;> omega

theorem exc_card_absurd {Jb : Type} [Group Jb] (hq : CFSG.Open.IsQuasisimple Jb)
    (hexc : IsSLThreeExc Jb ∨ IsSUThreeExc Jb) (k : ℕ)
    (hd : Nat.card Jb ∣ 3 ^ k * 5515776) : False := by
  rcases hexc with ⟨K, _, _, h9, ⟨e⟩⟩ | ⟨K, _, _, q, hc, h9, ⟨e⟩⟩
  · set r := Nat.card K with hr
    have hcard : Nat.card Jb = r ^ 3 * ((r ^ 3 - 1) * (r ^ 2 - 1)) := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Quasithin.H13.SL3.card_statedSL
    have hpos : 2 ≤ r := by
      have := Finite.one_lt_card (α := K)
      omega
    have h4 : r = 4 := by
      refine eq_four_of_cube_dvd h9 (le_of_cube_dvd (k := k) (by omega) ?_) hpos
      exact (Dvd.intro _ rfl).trans (hcard ▸ hd)
    rw [hcard, h4] at hd
    have h5 : 5 ∣ 3 ^ k * 5515776 := (by norm_num : 5 ∣ 4 ^ 3 * ((4 ^ 3 - 1) * (4 ^ 2 - 1))).trans hd
    rcases (Nat.Prime.dvd_mul (by norm_num)).1 h5 with h | h
    · have := (Nat.Prime.dvd_of_dvd_pow (by norm_num) h)
      omega
    · omega
  · have hcard : Nat.card Jb = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) := by
      rw [Nat.card_congr e.toEquiv]
      exact card_statedSU_three_of' hc
    have hpos : 2 ≤ q := by omega
    have h2 : q = 2 := by
      refine eq_two_of_cube_dvd h9 (le_of_cube_dvd (k := k) (by omega) ?_) hpos
      exact (Dvd.dvd.mul_right (Dvd.dvd.mul_right dvd_rfl _) _).trans (hcard ▸ hd)
    subst h2
    have hsol := CFSG.Quasithin.isSolvable_statedSU_one (F := K) (by simpa using hc)
    rw [pow_one] at hsol
    have hJ : Group.IsSolvable Jb :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    have : Group.IsPerfect Jb := ⟨hq.1⟩
    have : Nontrivial Jb := CFSG.ComponentClassification.Quasisimple.nontrivial hq
    exact Group.IsPerfect.not_isSolvable Jb hJ

end CFSG.HardMathSupport.Solomon.Coordinator
