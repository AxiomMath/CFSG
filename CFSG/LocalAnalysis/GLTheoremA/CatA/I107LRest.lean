module

public import CFSG.LocalAnalysis.GLTheoremA.S9.YS07Cat18
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107LCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107LAltM
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107LEich

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I107L

open CFSG.Open CFSG.Assembly

@[expose] def TwoRankLowExc : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (lab : GLALabel), IsSimpleGroup S → Rk2IsLabel S lab → GLAInLambda2 lab →
    ¬ exempt107 lab →
    (lab.tag = .twB2 ∨ lab.tag = .triD4 ∨ lab.tag = .G2 ∨ lab.tag = .F4 ∨ lab.tag = .twF4 ∨ lab.tag = .E6 ∨
      lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .twE6) →
    twoRankLow107 lab ≤ CFSG.Open.pRank 2 (⊤ : Subgroup S)

theorem twoRankLow_twA_holds (S : Type) [Group S] [Finite S] (lab : GLALabel) (hS : IsSimpleGroup S)
    (hrk : Rk2IsLabel S lab) (ht : lab.tag = .twA) :
    twoRankLow107 lab ≤ CFSG.Open.pRank 2 (⊤ : Subgroup S) := by
  have hlab := rk2IsLabel_inLambda2 hrk
  have hraw := rk2IsLabel_rawDatum hrk
  obtain ⟨tag, rank, n⟩ := lab
  obtain rfl : tag = .twA := ht
  have hn : 1 ≤ n := hlab.1
  have hr : 2 ≤ rank := hlab.2.1
  have hkey : twoRankLow107 ⟨.twA, rank, n⟩ = n * ((rank + 1) / 2) ^ 2 := rfl
  rw [hkey]
  dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum,
    CFSG.Assembly.LargeEvenRecipeUnitary] at hraw
  obtain ⟨K, hf, hfin, hK, hQ⟩ := hraw
  obtain ⟨hsR, hna, ⟨θ⟩⟩ := hQ
  haveI : Finite (LargeEvenProj (LargeEvenSUGroup (Fin (rank + 1)) K (2 ^ n))) :=
    Finite.of_equiv _ θ.toEquiv
  rw [pRank_eq_of_quotient θ hna]
  exact pRank_herm_ge hn (by omega) (by omega) hK

theorem twoRankLow_twD3_holds (S : Type) [Group S] [Finite S] (lab : GLALabel) (hS : IsSimpleGroup S)
    (hrk : Rk2IsLabel S lab) (ht : lab.tag = .twD) (hr : lab.rank = 3) :
    twoRankLow107 lab ≤ CFSG.Open.pRank 2 (⊤ : Subgroup S) := by
  have hlab := rk2IsLabel_inLambda2 hrk
  have hraw := rk2IsLabel_rawDatum hrk
  obtain ⟨tag, rank, n⟩ := lab
  obtain rfl : rank = 3 := hr
  obtain rfl : tag = .twD := ht
  have hn : 1 ≤ n := hlab.1
  have hkey : twoRankLow107 ⟨.twD, 3, n⟩ ≤ n * 2 ^ 2 := by
    simp only [twoRankLow107]
    exact max_le (le_of_eq (by norm_num)) (Nat.mul_le_mul_left _ (by norm_num))
  refine le_trans hkey ?_
  dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum,
    CFSG.Assembly.LargeEvenRecipeUnitary] at hraw
  simp only [show ¬ (3 : ℕ) = 2 by norm_num, if_false, if_true] at hraw
  obtain ⟨K, hf, hfin, hK, hQ⟩ := hraw
  obtain ⟨hsR, hna, ⟨θ⟩⟩ := hQ
  haveI : Finite (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n))) :=
    Finite.of_equiv _ θ.toEquiv
  rw [pRank_eq_of_quotient θ hna]
  exact pRank_herm_ge hn (by norm_num) (by norm_num) hK

theorem twoRankLow_D_ge4 (S : Type) [Group S] [Finite S] (lab : GLALabel) (hS : IsSimpleGroup S)
    (hrk : Rk2IsLabel S lab) (ht : lab.tag = .D) (hr : 4 ≤ lab.rank) :
    twoRankLow107 lab ≤ CFSG.Open.pRank 2 (⊤ : Subgroup S) := by
  have hlab := rk2IsLabel_inLambda2 hrk
  have hraw := rk2IsLabel_rawDatum hrk
  obtain ⟨tag, rank, n⟩ := lab
  obtain rfl : tag = .D := ht
  have hn : 1 ≤ n := hlab.1
  have hr' : 4 ≤ rank := hr
  have hne : rank ≠ 3 := by omega
  have hkey : twoRankLow107 ⟨.D, rank, n⟩ = n * Nat.choose rank 2 := by
    simp only [twoRankLow107, Nat.choose_two_right]
  rw [hkey]
  dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] at hraw
  rw [if_neg hne] at hraw
  dsimp only [CFSG.Assembly.LargeEvenRecipeOmegaPlus] at hraw
  obtain ⟨K, hf, hfin, hK, hQ⟩ := hraw
  obtain ⟨hsR, hna, ⟨θ⟩⟩ := hQ
  haveI : Finite (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K rank))) :=
    Finite.of_equiv _ θ.toEquiv
  rw [pRank_eq_of_quotient θ hna]
  exact pRank_alt_plus_ge hn (by omega) hK

theorem twoRankLow_twD_ge4 (S : Type) [Group S] [Finite S] (lab : GLALabel) (hS : IsSimpleGroup S)
    (hrk : Rk2IsLabel S lab) (ht : lab.tag = .twD) (hr : 4 ≤ lab.rank) :
    twoRankLow107 lab ≤ CFSG.Open.pRank 2 (⊤ : Subgroup S) := by
  have hlab := rk2IsLabel_inLambda2 hrk
  have hraw := rk2IsLabel_rawDatum hrk
  obtain ⟨tag, rank, n⟩ := lab
  obtain rfl : tag = .twD := ht
  have hr' : 4 ≤ rank := hr
  obtain ⟨m, rfl⟩ : ∃ m, rank = m + 1 := ⟨rank - 1, by omega⟩
  have hn : 1 ≤ n := hlab.1
  have hm3 : 3 ≤ m := by omega
  have hkey : twoRankLow107 ⟨.twD, m + 1, n⟩ =
      max (n * (2 * (m + 1) - 2)) (n * (m * (m - 1) / 2)) := by
    simp only [twoRankLow107, Nat.add_sub_cancel]
    have h12 : m + 1 - 2 = m - 1 := by omega
    rw [h12]
  rw [hkey]
  dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] at hraw
  rw [if_neg (show ¬ (m + 1 = 2) by omega), if_neg (show ¬ (m + 1 = 3) by omega)] at hraw
  dsimp only [CFSG.Assembly.LargeEvenRecipeOmegaMinus] at hraw
  obtain ⟨K, hf, hfin, hK, b, c, hirr, hQ⟩ := hraw
  obtain ⟨hsR, hna, ⟨θ⟩⟩ := hQ
  haveI : Finite (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) :=
    Finite.of_equiv _ θ.toEquiv
  rw [pRank_eq_of_quotient θ hna]
  rcases Nat.lt_or_ge m 5 with hm5 | hm5
  · have h := pRank_minus_eichler_ge hn hm3 hK b c hirr
    refine le_trans (max_le ?_ ?_) h
    · exact le_of_eq (by rw [show 2 * (m + 1) - 2 = 2 * m by omega])
    · refine Nat.mul_le_mul_left _ ?_
      interval_cases m <;> norm_num
  · have h := pRank_alt_minus_ge hn (by omega) hK b c
    have hch : 2 * m ≤ m.choose 2 := by
      rw [Nat.choose_two_right, Nat.le_div_iff_mul_le (by norm_num)]
      obtain ⟨s, rfl⟩ : ∃ s, m = s + 5 := ⟨m - 5, by omega⟩
      have h5 : s + 5 - 1 = s + 4 := by omega
      rw [h5]
      nlinarith
    refine le_trans (max_le ?_ ?_) h
    · exact Nat.mul_le_mul_left _ (by omega)
    · rw [← Nat.choose_two_right]

theorem twoRankLowRest_of_exc (h : TwoRankLowExc) : TwoRankLowRest := by
  intro S _ _ lab hS hrk hlab hne hA
  obtain ⟨tag, rank, n⟩ := lab
  cases tag
  case A => exact absurd rfl hA
  case twA => exact twoRankLow_twA_holds S _ hS hrk rfl
  case B => exact twoRankLow_sp S _ hS hrk (Or.inl rfl)
  case C => exact twoRankLow_sp S _ hS hrk (Or.inr rfl)
  case D =>
    have h3 : 3 ≤ rank := hlab.2
    by_cases hr : rank = 3
    · exact twoRankLow_lin_D3 S _ hS hrk rfl hr
    · exact twoRankLow_D_ge4 S _ hS hrk rfl (show 4 ≤ rank by omega)
  case twD =>
    have h2 : 2 ≤ rank := hlab.2
    by_cases hr2 : rank = 2
    · exact twoRankLow_lin_twD2 S _ hS hrk rfl hr2
    by_cases hr3 : rank = 3
    · exact twoRankLow_twD3_holds S _ hS hrk rfl hr3
    · exact twoRankLow_twD_ge4 S _ hS hrk rfl (show 4 ≤ rank by omega)
  case E6 => exact h S _ hS hrk hlab hne (by simp)
  case E7 => exact h S _ hS hrk hlab hne (by simp)
  case E8 => exact h S _ hS hrk hlab hne (by simp)
  case F4 => exact h S _ hS hrk hlab hne (by simp)
  case twE6 => exact h S _ hS hrk hlab hne (by simp)
  case triD4 => exact h S _ hS hrk hlab hne (by simp)
  case G2 => exact h S _ hS hrk hlab hne (by simp)
  case twB2 => exact h S _ hS hrk hlab hne (by simp)
  case twF4 => exact h S _ hS hrk hlab hne (by simp)
  case B2der =>
    have h0 : twoRankLow107 ⟨.B2der, rank, n⟩ = 0 := rfl
    rw [h0]
    exact Nat.zero_le _
  case G2der =>
    have h0 : twoRankLow107 ⟨.G2der, rank, n⟩ = 0 := rfl
    rw [h0]
    exact Nat.zero_le _
  case twF4der =>
    have h0 : twoRankLow107 ⟨.twF4der, rank, n⟩ = 0 := rfl
    rw [h0]
    exact Nat.zero_le _

end CFSG.LocalAnalysis.GLTheoremA.I107L

end
