module

public import CFSG.CGT.PushingUpLit.Statements
public import CFSG.CGT.PushingUp.BlockOrder
public import CFSG.CGT.PushingUp.ResidualTwo
public import CFSG.GH74.SectionalRank

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.Assembly
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

variable {G : Type} [Group G] [Finite G]

theorem exists_isMaximalInClassXG {X : Subgroup G} (hX : InClassXG X) :
    ∃ X' : Subgroup G, IsMaximalInClassXG X' := by
  obtain ⟨X', hX', hmax⟩ := Set.exists_max_image {Y : Subgroup G | InClassXG Y}
    (fun Y => Nat.card Y) (Set.toFinite _) ⟨X, hX⟩
  exact ⟨X', hX', fun Y hY hXY =>
    (Subgroup.eq_of_le_of_card_ge (arrow_le hXY) (hmax Y hY)).symm⟩

theorem threeTwo_of_block [IsSimpleGroup G] (hK : KProper InCatalog G)
    (hTwo : AschbacherTheoremTwoK) (hSol : SolomonAlternatingBlockK)
    (hchar : CFSG.Assembly.IsCharTwoType G) {X M : Subgroup G} (hXcl : InClassX ↥X)
    (hM : IsMaximalTwoLocal M) (hXM : X ≤ M) (hsub : (X.subgroupOf M).IsSubnormal)
    (hu : maximalTwoLocalsContaining (X : Set G) = {M}) : ThreeTwoConclusion G := by
  rcases hXcl.2 with ⟨n, hn, halt⟩ | ⟨n, hn, hsl⟩
  · exact Or.inr (Or.inr (hSol G hK inferInstance hchar M X hM hXM hsub hXcl ⟨n, hn, halt⟩ hu))
  · have hn2 : 2 ≤ n := by
      by_contra hlt
      have : n = 1 := by omega
      subst this
      exact not_isNaturalSLTwoModule_one hXcl.1 hsl
    rcases hTwo G hK inferInstance hchar X M hXcl hM hXM hsub hu n hn2 hsl with h | h | ⟨-, h⟩
    · exact Or.inl ⟨n, hn, Or.inr (Or.inr (Or.inl h))⟩
    · exact Or.inl ⟨n, hn, Or.inr (Or.inr (Or.inr h))⟩
    · exact Or.inr (Or.inr (by
        have := CFSG.GH74.sectionalTwoRankLE_sectionalTwoRank (X := G)
        rw [h] at this
        exact this))

end CFSG.CGT.PushingUpLit
