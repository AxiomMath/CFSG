module

public import CFSG.Quasithin.Background.A3Structure316
import CFSG.GroupTheory.WeirSylow.CrossRankLinear
import CFSG.GroupTheory.WeirSylow.Unitary
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevSigma

public section

namespace CFSG.GroupTheory.WeirSylow

open CFSG.Open

theorem pRank_top_statedGU_eq {p : ℕ} [Fact p.Prime] (hp : Odd p) {L : Type} [Field L]
    [Finite L] {q n : ℕ} (hL : Nat.card L = q ^ 2) (hpq : ¬ p ∣ q) (hn : 1 ≤ n) :
    CFSG.Open.pRank p (⊤ : Subgroup (CFSG.Quasithin.StatedGU n q L)) =
      n / orderOf (-(q : ZMod p)) := by
  haveI : Fintype L := Fintype.ofFinite L
  have hLc : Fintype.card L = q ^ 2 := by rwa [← Nat.card_eq_fintype_card]
  have hq2 : 2 ≤ q := by
    have h1 : 2 ≤ q ^ 2 := by rw [← hLc]; exact Fintype.one_lt_card
    nlinarith [Nat.zero_le q]
  have hc : ¬ (p : ℤ) ∣ -(q : ℤ) := by
    rw [dvd_neg]
    exact_mod_cast hpq
  have hc2 : 2 ≤ |-(q : ℤ)| := by
    rw [abs_neg, abs_of_nonneg (by positivity)]
    exact_mod_cast hq2
  have hpos : 0 < orderOf (-(q : ZMod p)) := by
    rw [← ordMod_neg_natCast]
    exact ordMod_pos hc
  have ha : 1 ≤ padicValInt p ((-(q : ℤ)) ^ orderOf (-(q : ZMod p)) - 1) := by
    have hdvd : (p : ℤ) ∣ (-(q : ℤ)) ^ orderOf (-(q : ZMod p)) - 1 := by
      rw [dvd_pow_sub_one_iff, ordMod_neg_natCast]
    have hne := pow_sub_one_ne_zero hc2 hpos.ne'
    exact one_le_padicValNat_of_dvd (by simpa using hne) (Int.natCast_dvd.1 hdvd)
  exact CFSG.LocalAnalysis.RankThreeUC.S15.RankChevProof.pRank_eq_of_sylow_sigmaModel (p := p)
    (e := orderOf (-(q : ZMod p)))
    (a := padicValInt p ((-(q : ℤ)) ^ orderOf (-(q : ZMod p)) - 1)) (N := n) ha
    (fun P => sylow_GU hp L hLc hpq hn P)

private theorem statedSU_le_statedGU {n q : ℕ} {L : Type} [Field L] :
    StatedSU n q L ≤ CFSG.Quasithin.StatedGU n q L := by
  unfold StatedSU CFSG.Quasithin.StatedGU
  exact (Subgroup.closure_le _).2 fun A hA => Subgroup.subset_closure hA.2

theorem pRank_top_statedSU_le {p : ℕ} [Fact p.Prime] (hp : Odd p) {L : Type} [Field L]
    [Finite L] {q n : ℕ} (hL : Nat.card L = q ^ 2) (hpq : ¬ p ∣ q) (hn : 1 ≤ n) :
    CFSG.Open.pRank p (⊤ : Subgroup (StatedSU n q L)) ≤ n / orderOf (-(q : ZMod p)) := by
  have h := CFSG.SectionRank.pRank_top_le_of_injective (p := p)
    (Fact.out : p.Prime).one_lt
    (Subgroup.inclusion (statedSU_le_statedGU (n := n) (q := q) (L := L)))
    (Subgroup.inclusion_injective _)
  rw [pRank_top_statedGU_eq hp hL hpq hn] at h
  exact h

private theorem orderOf_neg_natCast_eq_two_of_dvd_sub_one {p q : ℕ} [Fact p.Prime] (hp : Odd p)
    (hq : 1 ≤ q) (h : p ∣ q - 1) : orderOf (-(q : ZMod p)) = 2 := by
  have h1 : (q : ZMod p) = 1 := by
    have := (ZMod.natCast_eq_zero_iff (q - 1) p).2 h
    rw [Nat.cast_sub hq, Nat.cast_one, sub_eq_zero] at this
    exact this
  have hp2 : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hp) even_two
  rw [h1]
  have := orderOf_neg_one (R := ZMod p)
  rwa [if_neg hp2] at this

theorem pRank_top_statedProj_statedSU_le_div_two {p : ℕ} [Fact p.Prime] (hp : Odd p)
    {L : Type} [Field L] [Finite L] {q n : ℕ} (hL : Nat.card L = q ^ 2) (hpn : ¬ p ∣ n)
    (h : p ∣ q - 1) :
    CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSU n q L))) ≤ n / 2 := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 fun h0 => hpn (h0 ▸ dvd_zero p)
  have hq1 : 1 ≤ q := by
    have h1 : 2 ≤ q ^ 2 := by rw [← hL]; exact Finite.one_lt_card
    by_contra hq0
    have : q = 0 := by omega
    simp [this] at h1
  have hpq : ¬ p ∣ q := fun hd => by
    have h1 := (Nat.dvd_add_right h).1 (by rwa [Nat.sub_add_cancel hq1])
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.1 h1)
  rw [pRank_top_statedProj_eq hpn fun c hc => pow_eq_one_of_scalar_mem_statedSL
    (CFSG.Open.StatedAPI.statedSU_le_statedSL n q L hc)]
  have := pRank_top_statedSU_le hp hL hpq hn
  rwa [orderOf_neg_natCast_eq_two_of_dvd_sub_one hp hq1 h] at this

theorem pRank_top_statedProj_statedSU_le_div_three {p : ℕ} [Fact p.Prime] (hp : Odd p)
    {L : Type} [Field L] [Finite L] {q n : ℕ} (hL : Nat.card L = q ^ 2) (hpq : ¬ p ∣ q)
    (hpq2 : ¬ p ∣ q ^ 2 - 1) (hn : 1 ≤ n) :
    CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSU n q L))) ≤ n / 3 := by
  have hd : ¬ p ∣ Nat.card L - 1 := by rwa [hL]
  rw [pRank_top_statedProj_eq hd fun c _ => by
    rw [← Nat.card_units]; exact pow_card_eq_one']
  have hle := pRank_top_statedSU_le hp hL hpq hn
  have he : 3 ≤ orderOf (-(q : ZMod p)) := by
    rw [← ordMod_neg_natCast]
    refine three_le_ordMod_of_not_dvd_sq_sub_one ?_ ?_
    · rw [dvd_neg]; exact_mod_cast hpq
    · have := not_intCast_dvd_sq_sub_one_of_not_dvd hpq2
      rwa [← neg_sq] at this
  exact hle.trans (Nat.div_le_div_left he (by norm_num))

end CFSG.GroupTheory.WeirSylow
