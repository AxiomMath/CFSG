module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.TypeSplit
public import CFSG.RankThree.PartOne.LIT.RankPSL3
public import CFSG.RankThree.PartOne.LIT.RankMatrix

public section

namespace CFSG.Quasithin.B69K

open CFSG.Open

theorem pRank_le_two_of_psl2 {K : Type} [Group K] [Finite K] {f : ℕ}
    (h : StatedClassicalModel K .PSL 2 2 f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup K) ≤ 2 := by
  obtain ⟨e⟩ := CFSG.RankThree.PartOne.projSL_of_statedClassicalModel h
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
  exact CFSG.RankThree.PartOne.LIT.pRank_projSL_two_le (K := GaloisField 2 f) hp hp2
    (CFSG.RankThree.PartOne.LIT.natCast_ne_zero_of_charTwo hp hp2)

theorem pRank_le_two_of_psl3 {K : Type} [Group K] [Finite K] {f : ℕ}
    (h : StatedClassicalModel K .PSL 3 2 f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup K) ≤ 2 := by
  have hf : 1 ≤ f := h.1.2.1
  obtain ⟨e⟩ := CFSG.RankThree.PartOne.projSL_of_statedClassicalModel h
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
  exact CFSG.RankThree.PartOne.LIT.pRank_projSL_three_le (K := GaloisField 2 f) hf
    (GaloisField.card 2 f (by omega)) hp hp2

theorem pRank_le_two_of_psu3 {K : Type} [Group K] [Finite K] {f : ℕ}
    (h : StatedClassicalModel K .PSU 3 2 f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup K) ≤ 2 := by
  have hf : 1 ≤ f := h.1.2.1
  obtain ⟨e⟩ := CFSG.RankThree.PartOne.projSU_of_statedClassicalModel h
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
  exact CFSG.RankThree.PartOne.LIT.pRank_projSU_three_le hf hp hp2

theorem pRank_le_two_of_psp2 {K : Type} [Group K] [Finite K] {f : ℕ}
    (h : StatedClassicalModel K .PSp 2 2 f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup K) ≤ 2 := by
  obtain ⟨e⟩ := CFSG.RankThree.PartOne.projSp_of_statedClassicalModel h
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
  exact CFSG.RankThree.PartOne.LIT.pRank_projSp_two_le (K := GaloisField 2 f) hp hp2
    (CFSG.RankThree.PartOne.LIT.natCast_ne_zero_of_charTwo hp hp2)

theorem natCard_altGroup_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup]
  norm_num [Nat.factorial]

theorem natCard_altGroup_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup]
  norm_num [Nat.factorial]

theorem prime_cube_not_dvd_sixty {p : ℕ} (hp : p.Prime) : ¬ p ^ 3 ∣ 60 := by
  intro h
  have hle : p ^ 3 ≤ 60 := Nat.le_of_dvd (by norm_num) h
  have hp4 : p < 4 := by
    by_contra hc
    exact absurd (le_trans (Nat.pow_le_pow_left (not_lt.mp hc) 3) hle) (by norm_num)
  interval_cases p <;> norm_num at *

theorem prime_cube_not_dvd_360 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ^ 3 ∣ 360 := by
  intro h
  have hle : p ^ 3 ≤ 360 := Nat.le_of_dvd (by norm_num) h
  have hp8 : p < 8 := by
    by_contra hc
    exact absurd (le_trans (Nat.pow_le_pow_left (not_lt.mp hc) 3) hle) (by norm_num)
  interval_cases p <;> norm_num at *

theorem pRank_le_two_of_alt5 {K : Type} [Group K] [Finite K] (h : CFSG.Quasithin.IsAlt 5 K)
    {p : ℕ} (hp : p.Prime) : CFSG.Open.pRank p (⊤ : Subgroup K) ≤ 2 := by
  obtain ⟨e⟩ := h
  apply CFSG.RankThree.PartTwo.Census.pRank_le_two_of_not_dvd hp
  rw [Nat.card_congr e.toEquiv, natCard_altGroup_five]
  exact prime_cube_not_dvd_sixty hp

theorem pRank_le_two_of_alt6 {K : Type} [Group K] [Finite K] (h : CFSG.Quasithin.IsAlt 6 K)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : CFSG.Open.pRank p (⊤ : Subgroup K) ≤ 2 := by
  obtain ⟨e⟩ := h
  apply CFSG.RankThree.PartTwo.Census.pRank_le_two_of_not_dvd hp
  rw [Nat.card_congr e.toEquiv, natCard_altGroup_six]
  exact prime_cube_not_dvd_360 hp hp2

theorem pRank_le_two_of_survivor {K : Type} [Group K] [Finite K] (hK : Survivor K)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : CFSG.Open.pRank p (⊤ : Subgroup K) ≤ 2 := by
  rcases hK with ⟨f, h⟩ | ⟨f, h⟩ | ⟨f, h⟩ | ⟨f, h⟩ | h | h
  · exact pRank_le_two_of_psl2 h hp hp2
  · exact pRank_le_two_of_psl3 h hp hp2
  · exact pRank_le_two_of_psu3 h hp hp2
  · exact pRank_le_two_of_psp2 h hp hp2
  · exact pRank_le_two_of_alt5 h hp
  · exact pRank_le_two_of_alt6 h hp hp2

end CFSG.Quasithin.B69K

end
