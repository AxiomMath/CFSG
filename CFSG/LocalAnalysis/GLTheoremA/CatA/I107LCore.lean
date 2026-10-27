module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107F4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107GLow
public import CFSG.GH74.Filter.Orthogonal.SymplecticSix

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I107L

open CFSG.Open CFSG.Assembly

theorem pRank_eq_of_quotient {S R : Type} [Group S] [Finite S] [Group R] [Finite R] [IsSimpleGroup S]
    (θ : S ⧸ Subgroup.center S ≃* R) (hna : ∃ a b : R, a * b ≠ b * a) :
    CFSG.Open.pRank 2 (⊤ : Subgroup S) = CFSG.Open.pRank 2 (⊤ : Subgroup R) := by
  have hZ := center_eq_bot_of_quotient_nonab θ hna
  let e : S ≃* R :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans θ
  exact CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 2) e

theorem choose_succ_two (r : ℕ) : (r + 1).choose 2 = r * (r + 1) / 2 := by
  rw [Nat.choose_two_right, Nat.add_sub_cancel, mul_comm]

theorem two_mul_sub_one_le_choose (r : ℕ) (hr : 1 ≤ r) : 2 * r - 1 ≤ (r + 1).choose 2 := by
  rw [choose_succ_two, Nat.le_div_iff_mul_le (by norm_num)]
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have h1 : 2 * (s + 1) - 1 = 2 * s + 1 := by omega
  rw [h1]
  nlinarith [Nat.le_mul_self s]

theorem twoRankLow_sp (S : Type) [Group S] [Finite S] (lab : GLALabel) (hS : IsSimpleGroup S)
    (hrk : Rk2IsLabel S lab) (ht : lab.tag = .B ∨ lab.tag = .C) :
    twoRankLow107 lab ≤ CFSG.Open.pRank 2 (⊤ : Subgroup S) := by
  have hlab := rk2IsLabel_inLambda2 hrk
  have hraw := rk2IsLabel_rawDatum hrk
  obtain ⟨tag, rank, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  have hr : 2 ≤ rank := by
    rcases ht with rfl | rfl
    · exact hlab.2.1
    · exact hlab.2.1
  have hkey : twoRankLow107 ⟨tag, rank, n⟩ ≤ n * (rank + 1).choose 2 := by
    rcases ht with rfl | rfl
    · simp only [twoRankLow107]
      refine max_le (Nat.mul_le_mul_left _ (two_mul_sub_one_le_choose rank (by omega))) ?_
      rw [choose_succ_two]
      exact Nat.mul_le_mul_left _ (Nat.div_le_div_right (Nat.mul_le_mul_left _ (by omega)))
    · simp only [twoRankLow107, choose_succ_two]
      exact le_of_eq (by ring_nf)
  refine le_trans hkey ?_
  rcases ht with rfl | rfl
  all_goals
    dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum,
      CFSG.Assembly.LargeEvenRecipeSymplectic] at hraw
    obtain ⟨K, hf, hfin, hK, hQ⟩ := hraw
    obtain ⟨hsR, hna, ⟨θ⟩⟩ := hQ
    replace θ : S ⧸ Subgroup.center S ≃* LargeEvenProj (LargeEvenSpGroup K rank) := θ
    haveI : Finite (LargeEvenProj (LargeEvenSpGroup K rank)) :=
      Finite.of_equiv _ θ.toEquiv
    rw [pRank_eq_of_quotient θ hna]
    exact CFSG.GH74.Filter.le_pRank_Sp_sym (K := K) (n := rank) (by omega) (p := 2) (f := n) hK

theorem twoRankLow_lin_D3 (S : Type) [Group S] [Finite S] (lab : GLALabel) (hS : IsSimpleGroup S)
    (hrk : Rk2IsLabel S lab) (ht : lab.tag = .D) (hr : lab.rank = 3) :
    twoRankLow107 lab ≤ CFSG.Open.pRank 2 (⊤ : Subgroup S) := by
  have hlab := rk2IsLabel_inLambda2 hrk
  have hraw := rk2IsLabel_rawDatum hrk
  obtain ⟨tag, rank, n⟩ := lab
  obtain rfl : rank = 3 := hr
  obtain rfl : tag = .D := ht
  have hn : 1 ≤ n := hlab.1
  have hkey : twoRankLow107 ⟨.D, 3, n⟩ ≤ n * (2 * (4 - 2)) := by
    simp only [twoRankLow107]
    exact Nat.mul_le_mul_left _ (by norm_num)
  refine le_trans hkey ?_
  dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum,
    CFSG.Assembly.LargeEvenRecipeLinear] at hraw
  obtain ⟨K, hf, hfin, hK, hQ⟩ := hraw
  obtain ⟨hsR, hna, ⟨θ⟩⟩ := hQ
  haveI : Finite (LargeEvenProj (LargeEvenSLGroup (Fin 4) K)) :=
    Finite.of_equiv _ θ.toEquiv
  rw [pRank_eq_of_quotient θ hna]
  exact I107G.pRank_unipProj_ge (K := K) (d := 4) (k := 2) (n := n) (by norm_num) (by norm_num) hn hK

theorem twoRankLow_lin_twD2 (S : Type) [Group S] [Finite S] (lab : GLALabel) (hS : IsSimpleGroup S)
    (hrk : Rk2IsLabel S lab) (ht : lab.tag = .twD) (hr : lab.rank = 2) :
    twoRankLow107 lab ≤ CFSG.Open.pRank 2 (⊤ : Subgroup S) := by
  have hlab := rk2IsLabel_inLambda2 hrk
  have hraw := rk2IsLabel_rawDatum hrk
  obtain ⟨tag, rank, n⟩ := lab
  obtain rfl : rank = 2 := hr
  obtain rfl : tag = .twD := ht
  have hn : 1 ≤ n := hlab.1
  have hkey : twoRankLow107 ⟨.twD, 2, n⟩ ≤ (2 * n) * (1 * (2 - 1)) := by
    simp only [twoRankLow107]
    exact max_le (le_of_eq (by ring)) (Nat.zero_le _)
  refine le_trans hkey ?_
  dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum,
    CFSG.Assembly.LargeEvenRecipeLinear] at hraw
  obtain ⟨K, hf, hfin, hK, hQ⟩ := hraw
  obtain ⟨hsR, hna, ⟨θ⟩⟩ := hQ
  haveI : Finite (LargeEvenProj (LargeEvenSLGroup (Fin 2) K)) :=
    Finite.of_equiv _ θ.toEquiv
  have hK' : Nat.card K = 2 ^ (2 * n) := by
    rw [hK, ← pow_mul, mul_comm]
  rw [pRank_eq_of_quotient θ hna]
  exact I107G.pRank_unipProj_ge (K := K) (d := 2) (k := 1) (n := 2 * n) (by norm_num) (by norm_num) (by omega) hK'

end CFSG.LocalAnalysis.GLTheoremA.I107L

end
