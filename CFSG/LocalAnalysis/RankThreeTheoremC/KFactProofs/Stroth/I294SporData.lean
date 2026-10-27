module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Inputs
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29Spor

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

@[expose] def SporadicThreeRankThree : Prop :=
  ∀ (s : TauCeti.SporadicName) [Finite (TauCeti.CFSGIndex.sporadic s).Group],
    CFSG.Open.pRank 3 (⊤ : Subgroup (TauCeti.CFSGIndex.sporadic s).Group) = 3 →
    3 ^ 4 ∣ Nat.card (TauCeti.CFSGIndex.sporadic s).Group → s = .J3

@[expose] def J3ThreeCentralizer : Prop :=
  ∀ [Finite (TauCeti.CFSGIndex.sporadic .J3).Group] (x : (TauCeti.CFSGIndex.sporadic .J3).Group),
    orderOf x = 3 →
      3 ^ 3 ∣ Nat.card (Subgroup.centralizer ({x} : Set (TauCeti.CFSGIndex.sporadic .J3).Group))

theorem sporadicCentralizerPPart_of_parts
    (hR : CFSG.LocalAnalysis.RankFourTheoremC.SporadicCentralizerRank)
    (hT : SporadicThreeRankThree) (hJ : J3ThreeCentralizer) : SporadicCentralizerPPart := by
  intro s p hp hp2 _ hrank h4 x hx
  by_cases hp3 : p = 3
  · subst hp3
    obtain rfl := hT s hrank h4
    exact hJ x hx
  · have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
    have h3 := hR s p hp hp5 _ ⟨MulEquiv.refl _⟩ hrank.ge x hx
    obtain ⟨E, hE, -, hcard⟩ :=
      CFSG.SectionRank.exists_pRank hp.one_lt
        (Subgroup.centralizer ({x} : Set (TauCeti.CFSGIndex.sporadic s).Group))
    exact (pow_dvd_pow p h3).trans (hcard ▸ Subgroup.card_dvd_of_le hE)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
