module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankLists
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Vocab
public import CFSG.Quasithin.Background.A1cRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def IsRankTwoType : TauCeti.LieTypeIndex → Prop
  | .G2 Q => Q.p = 2
  | .A 2 Q => Q.p = 2
  | .B 2 Q => Q.p = 2
  | .twistedA 3 Q => Q.p = 2
  | .twistedA 4 Q => Q.p = 2
  | _ => False

@[expose] def IsRankGeThreeType : TauCeti.LieTypeIndex → Prop
  | .A m Q => Q.p = 2 ∧ 3 ≤ m
  | .B m Q => Q.p = 2 ∧ 3 ≤ m
  | .D m Q => Q.p = 2 ∧ 4 ≤ m
  | .twistedD m Q => Q.p = 2 ∧ 4 ≤ m
  | .twistedA m Q => Q.p = 2 ∧ 5 ≤ m
  | _ => False

theorem isRankTwoType_or_isRankGeThreeType (d : TauCeti.LieTypeIndex)
    (hd : IsRankTwoPlus d) : IsRankTwoType d ∨ IsRankGeThreeType d := by
  cases d with
  | A l Q =>
      simp only [IsRankTwoPlus] at hd
      by_cases h2 : l = 2
      · subst h2; exact Or.inl hd.1
      · exact Or.inr ⟨hd.1, by omega⟩
  | B l Q =>
      simp only [IsRankTwoPlus] at hd
      by_cases h2 : l = 2
      · subst h2; exact Or.inl hd.1
      · exact Or.inr ⟨hd.1, by omega⟩
  | D l Q =>
      simp only [IsRankTwoPlus] at hd
      exact Or.inr ⟨hd.1, hd.2⟩
  | twistedD l Q =>
      simp only [IsRankTwoPlus] at hd
      exact Or.inr ⟨hd.1, hd.2⟩
  | twistedA l Q =>
      simp only [IsRankTwoPlus] at hd
      by_cases h3 : l = 3
      · subst h3; exact Or.inl hd.1
      · by_cases h4 : l = 4
        · subst h4; exact Or.inl hd.1
        · exact Or.inr ⟨hd.1, by omega⟩
  | G2 Q =>
      simp only [IsRankTwoPlus] at hd
      exact Or.inl hd
  | C l Q =>
      simp only [IsRankTwoPlus] at hd
  | E6 Q =>
      simp only [IsRankTwoPlus] at hd
  | E7 Q =>
      simp only [IsRankTwoPlus] at hd
  | E8 Q =>
      simp only [IsRankTwoPlus] at hd
  | F4 Q =>
      simp only [IsRankTwoPlus] at hd
  | twistedE6 Q =>
      simp only [IsRankTwoPlus] at hd
  | trialityD4 Q =>
      simp only [IsRankTwoPlus] at hd
  | suzuki n =>
      simp only [IsRankTwoPlus] at hd
  | reeG2 n =>
      simp only [IsRankTwoPlus] at hd
  | reeF4 n =>
      simp only [IsRankTwoPlus] at hd
  | tits =>
      simp only [IsRankTwoPlus] at hd

theorem one_lt_mS_of_isElemAbelian_le_gnA {X : Type} [Group X] [Finite X]
    {T Ti : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)} {q : ℕ} (hq : q.Prime)
    {E : Subgroup (X ⧸ gnC T)} (hle : E ≤ gnA T Ti Ls)
    (hE : IsElemAbelian q E) (hcard : Nat.card E = q ^ 2) :
    1 < mS T Ti q Ls := by
  have h2 : 2 ≤ CFSG.Open.pRank q (gnA T Ti Ls) :=
    CFSG.Quasithin.le_pRank hq hle hE hcard
  exact h2

end CFSG.LocalAnalysis.RankThreeUC.S15

end
