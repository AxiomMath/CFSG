module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81AutSectionOf
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81AutSectionEntries

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.AutSection

open CFSG.Open CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

theorem kFactNineThreeAutSection_of_sz
    (hSz : ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ 5 → ∀ d : TauCeti.ValidLieTypeIndex,
      d.1 = .suzuki 2 → ∀ (V : Type) [Group V] [Finite V], IsPGroup q V →
      Open.pRank q (⊤ : Subgroup V) ≤ 3 →
      ∀ (A : Subgroup (MulAut V)) (φ : ↥A →* (TauCeti.CFSGIndex.lie d).Group),
        ¬ Function.Surjective φ) :
    RankThreeTheoremC.KFactNineThreeAutSection :=
  kFactNineThreeAutSection_of_entries
    (fun _ hp hp2 hp3 _ hi hS _ _ _ hK => not_smallAutomizer_of_nineThree hp hp2 hp3 hi hS hK) hSz

end CFSG.LocalAnalysis.RankThreeTheoremC.AutSection
