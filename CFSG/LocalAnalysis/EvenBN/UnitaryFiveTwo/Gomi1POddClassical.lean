module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1POddArithA
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1POddArithD
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1POddSp
public import CFSG.ClassicalInvolution.Orders.Classical
public import CFSG.GH74.Filter.Small.RankThree
public import CFSG.GH74.SmallRanks.PSL

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P

open CFSG.Blueprint CFSG.Open CFSG.Assembly.LowTwoRank

theorem gomiOdd_six_le_twoRank {T : Type} [Group T] [Finite T] (E : Subgroup T)
    (hEcard : Nat.card E = 2 ^ 6) (hsq : ∀ x ∈ E, x * x = 1) : 6 ≤ twoRank T := by
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    intro x hx y hy
    calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right (hsq _ (E.mul_mem hx hy))).symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by
        rw [inv_eq_of_mul_eq_one_right (hsq x hx), inv_eq_of_mul_eq_one_right (hsq y hy)]
  exact CFSG.TwoRankLowerBound.Helpers.le_twoRank_of_elementary T E
    ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, fun x hx => by rw [pow_two]; exact hsq x hx⟩
    6 hEcard

theorem gomiOdd_false_of_two_pow_nine_dvd {N m : ℕ} (hm : Odd m) (hN : N = 2 ^ 8 * m)
    (h9 : 2 ^ 9 ∣ N) : False := by
  rw [hN] at h9
  have h : 2 ^ 8 * 2 ∣ 2 ^ 8 * m := by simpa [pow_succ] using h9
  have h2 : 2 ∣ m := Nat.dvd_of_mul_dvd_mul_left (by positivity) h
  exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h2)

theorem gomi1P_not_odd_lie_classical {T : Type} [Group T] [Finite T] {t : StatedLieTag}
    {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hc : StatedClassicalModel T t n p f)
    (hord : ∃ m : ℕ, Odd m ∧ Nat.card T = 2 ^ 8 * m)
    (hE : ∃ E : Subgroup T, Nat.card E = 2 ^ 6 ∧ (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧
      ∀ x ∈ E, x * x = 1) : False := by
  obtain ⟨m, hmodd, hcard⟩ := hord
  obtain ⟨E, hEcard, -, hEsq⟩ := hE
  have hq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hrank : 6 ≤ twoRank T := gomiOdd_six_le_twoRank E hEcard hEsq
  have hcard' := CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2 hc
  have h8 : 2 ^ 8 ∣ Nat.card T := ⟨m, hcard⟩
  have hhc := hc
  obtain ⟨hadm, hrest⟩ := hc
  cases t with
  | PSL =>
    obtain ⟨-, -, hn, -, -⟩ := hadm
    have hN := hcard'.1 rfl
    by_cases h2 : n = 2
    · subst h2
      have := CFSG.GH74.SmallRanks.twoRank_le_two_of_statedClassicalModel_PSL_two_odd hp hp2 hhc
      omega
    by_cases h3 : n = 3
    · subst h3
      have := CFSG.GH74.Filter.t_PSL_three_odd T p f hp2 hhc
      omega
    by_cases h4 : n = 4
    · subst h4
      rw [hN] at h8
      exact gomiOdd_false_of_two_pow_nine_dvd hmodd hcard
        (hN ▸ gomiOdd_ordA_three hq h8)
    · exact gomiOdd_false_of_two_pow_nine_dvd hmodd hcard
        (hN ▸ gomiOdd_two_pow_nine_dvd_ordA hq (by omega))
  | PSU =>
    obtain ⟨-, -, hn, -⟩ := hadm
    have hN := hcard'.2.1 rfl
    by_cases h3 : n = 3
    · subst h3
      have := CFSG.GH74.Filter.t_PSU_three_odd T p f hp2 hhc
      omega
    by_cases h4 : n = 4
    · subst h4
      rw [hN] at h8
      exact gomiOdd_false_of_two_pow_nine_dvd hmodd hcard
        (hN ▸ gomiOdd_ordTwistedA_three hq h8)
    · exact gomiOdd_false_of_two_pow_nine_dvd hmodd hcard
        (hN ▸ gomiOdd_two_pow_nine_dvd_ordTwistedA hq (by omega))
  | PSp =>
    obtain ⟨-, -, hn, -⟩ := hadm
    have hN := hcard'.2.2.1 rfl
    by_cases h2 : n = 2
    · subst h2
      obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hrest
      have hKodd : Odd (Nat.card K) := by rw [hK]; exact hq
      exact gomiOdd_false_of_statedProj_sp_two (gomiOdd_two_ne_zero hKodd) e E hEcard hEsq
    · exact gomiOdd_false_of_two_pow_nine_dvd hmodd hcard
        (hN ▸ gomiOdd_two_pow_nine_dvd_ordBC hq (by omega))
  | POmegaOdd =>
    obtain ⟨-, -, hn, -⟩ := hadm
    have hN := hcard'.2.2.2.1 rfl
    exact gomiOdd_false_of_two_pow_nine_dvd hmodd hcard
      (hN ▸ gomiOdd_two_pow_nine_dvd_ordBC hq (by omega))
  | POmegaPlus =>
    obtain ⟨-, -, hn⟩ := hadm
    have hN := hcard'.2.2.2.2.1 rfl
    exact gomiOdd_false_of_two_pow_nine_dvd hmodd hcard
      (hN ▸ gomiOdd_two_pow_nine_dvd_ordD hq hn)
  | POmegaMinus =>
    obtain ⟨-, -, hn⟩ := hadm
    have hN := hcard'.2.2.2.2.2 rfl
    exact gomiOdd_false_of_two_pow_nine_dvd hmodd hcard
      (hN ▸ gomiOdd_two_pow_nine_dvd_ordTwistedD hq hn)
  | _ => exact hrest.elim

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P
