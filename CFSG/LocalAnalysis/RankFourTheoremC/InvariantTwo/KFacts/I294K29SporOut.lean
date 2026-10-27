module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29Spor
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicOuter
public import CFSG.Sporadic.Bridge.Catalogue

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

section CertificateInstances


theorem sporadicOutOdd_holds : SporadicOutOdd := fun s p hp hp2 =>
  CFSG.AGLEmbedding.not_dvd_card_outer_sporadic
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group s p hp hp2

end CertificateInstances

section CertificateInstancesNative


theorem sporadicRankTable_of_native
    (h : ∀ (s : TauCeti.SporadicName) (p : ℕ), p.Prime → 5 ≤ p → ∀ (S : Type) [Group S]
      [Finite S], Nonempty (S ≃* CFSG.Blueprint.NativeSporadic.Carrier s) →
      3 ≤ CFSG.Open.pRank p (⊤ : Subgroup S) → SporadicRankThreePair s p) :
    SporadicRankTable := by
  intro s p hp hp5 S _ _ ⟨e⟩ h3
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group s
  exact h s p hp hp5 S ⟨e.trans b.symm⟩ h3

theorem sporadicClassWitnessAt_of_native {s : TauCeti.SporadicName} {p : ℕ}
    (h : ∀ (S : Type) [Group S] [Finite S],
      Nonempty (S ≃* CFSG.Blueprint.NativeSporadic.Carrier s) →
      ∀ x : S, orderOf x = p → RankThreeWitness p x) : SporadicClassWitnessAt s p := by
  intro S _ _ ⟨e⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group s
  exact h S ⟨e.trans b.symm⟩

end CertificateInstancesNative

end CFSG.LocalAnalysis.RankFourTheoremC
