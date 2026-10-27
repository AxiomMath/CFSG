module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81AutSectionEntriesLie
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81AutSectionEntriesSpor
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81AutSectionEntriesRee
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeList

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.AutSection

open CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111 (IsNineThreeIndex)

theorem not_smallAutomizer_of_nineThree
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) {i : TauCeti.CFSGIndex}
    (hi : IsNineThreeIndex p i)
    (hSz : ¬ (p = 5 ∧ ∃ d : TauCeti.ValidLieTypeIndex, i = .lie d ∧ d.1 = .suzuki 2))
    {K : Type} [Group K] [Finite K] (hK : Nonempty (K ≃* i.Group)) : ¬ SmallAutomizer p K := by
  obtain ⟨e⟩ := hK
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    rcases (show p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p by omega) with h | h | h | h
    · exact absurd h hp2
    · exact absurd h hp3
    · exact absurd (h ▸ hp) (by norm_num)
    · exact h
  haveI : Fact p.Prime := ⟨hp⟩
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating n hn =>
    rcases hi with ⟨rfl, -⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hp3
    · exact not_smallAutomizer_altTen e
  | sporadic s =>
    rcases hi with ⟨rfl, -⟩ | ⟨rfl, hs⟩ | ⟨rfl, hs⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hp3
    · exact not_smallAutomizer_sporFive hs e
    · exact not_smallAutomizer_sporSeven hs e
    · exact not_smallAutomizer_sporEleven e
  | lie d =>
    rcases hi with ⟨q, hq, h2, hdq⟩ | ⟨q, hq, hdq⟩ | hsp | ⟨q, hq, -, hdq⟩ | ⟨rfl, -⟩ |
      ⟨rfl, -⟩ | ⟨rfl, hdt | hdt | hdt⟩
    · exact not_smallAutomizer_linTwo hp5 hq h2 hdq e
    · exact not_smallAutomizer_unitary hp5 hq hdq e
    · exact not_smallAutomizer_spFour hp5 hsp e
    · exact not_smallAutomizer_linThree hp5 hq hdq e
    · exact absurd rfl hp3
    · exact absurd rfl hp3
    · exact absurd ⟨rfl, d, rfl, hdt⟩ hSz
    · exact not_smallAutomizer_tits hdt e
    · exact not_smallAutomizer_reeFFour hdt e

end CFSG.LocalAnalysis.RankThreeTheoremC.AutSection
