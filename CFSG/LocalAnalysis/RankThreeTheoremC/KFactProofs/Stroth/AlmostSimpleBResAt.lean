module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResAFamily

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevIndexTwo)

@[expose] def ChevTwoOuterFixesPairAt (P : ℕ → Prop) (F : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → P p → ∀ (L : Type) [Group L] [Finite L],
    CFSG.Open.pRank p (⊤ : Subgroup L) = 2 →
    (∃ d : TauCeti.ValidLieTypeIndex, IsChevIndexTwo d.1 ∧ F d.1 ∧
      Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group)) →
    ¬ (p = 3 ∧ IsLThreeTwo L) →
    ∀ α : MulAut L, α ∉ inner L → α ^ p = 1 → FixesIndepPair p α

theorem ChevTwoOuterFixesPair.of_three_geFive {F : TauCeti.LieTypeIndex → Prop}
    (h3 : ChevTwoOuterFixesPairAt (fun p => p = 3) F)
    (h5 : ChevTwoOuterFixesPairAt (fun p => 5 ≤ p) F) : ChevTwoOuterFixesPair F := by
  intro p hp hp2 L _ _ hrk hd hne α hα hαp
  by_cases hp3 : p = 3
  · exact h3 p hp hp2 hp3 L hrk hd hne α hα hαp
  · refine h5 p hp hp2 ?_ L hrk hd hne α hα hαp
    by_contra h
    have h2 := hp.two_le
    have h4 : p = 4 := by omega
    subst h4
    exact absurd hp (by norm_num)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
