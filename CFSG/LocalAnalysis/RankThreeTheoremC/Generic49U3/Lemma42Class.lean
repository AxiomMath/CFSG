module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericListPrune3
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1Alt
public import CFSG.LocalAnalysis.AGLEmbedding.IsolatedVertex
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup CFSG.AGLEmbedding
open CFSG.RankThree.PartOne (SectionsForceEvenRankFour)
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.RankThree.PartOne.Census3 (IsoLie)

theorem isRankTwoSEGroupE3_of_isRankTwoSEGroup {G : Type} [Group G] [Finite G] (hS : Setting G)
    {p : ℕ} (hp : p ∈ rankThreeSigmaA G) (hp5 : 5 ≤ p) {H : Subgroup G} {Q : Type} [Group Q]
    (ψ : ↥H →* Q) (hψ : Function.Surjective ψ)
    (hFi : ¬ Nonempty (Q ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi22).Group))
    (hlist : IsRankTwoSEGroup p Q ∨ (p = 5 ∧ IsoLie Q (.suzuki 2))) :
    IsRankTwoSEGroupE3 p Q ∨ (p = 5 ∧ IsoLie Q (.suzuki 2)) := by
  rcases hlist with hSE | hSz
  · refine Or.inl ?_
    rcases hSE with ⟨hf, ⟨f⟩⟩ | ⟨q, hq1, hq2, hl⟩ | ⟨h5', ⟨f⟩⟩ | ⟨h3, -⟩ | ⟨h5', h'⟩ |
      ⟨h11, ⟨f⟩⟩
    · exact Or.inl ⟨hf, ⟨f⟩⟩
    · exact Or.inr (Or.inl ⟨q, hq1, hq2, hl⟩)
    · by_cases hp5' : p = 5
      · subst hp5'
        exact Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl ⟨f⟩⟩))
      · exfalso
        have hprime : p.Prime := sigmaA_prime p hp
        have h6 : p ≠ 6 := by
          rintro rfl
          exact absurd hprime (by decide)
        exact false_of_section_alternating hS.rank (n := 2 * p) (by omega) (H := H)
          (f.toMonoidHom.comp ψ) (f.surjective.comp hψ)
    · exact absurd h3 (by omega)
    · rcases h' with hl | ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
      · exact Or.inr (Or.inr (Or.inl ⟨h5', Or.inr (Or.inl hl)⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨h5', Or.inr (Or.inr ⟨f⟩)⟩))
      · exact (hFi ⟨f⟩).elim
    · exact Or.inr (Or.inr (Or.inr ⟨h11, ⟨f⟩⟩))
  · exact Or.inr hSz

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
