module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.P1ThreeSporOrders
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.P1ThreeSporRows

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint

theorem sporMidAt_of_offList
    (hcard : ∀ s, Nat.card (NativeSporadic.Carrier s) = sporOrd s)
    (s : TauCeti.SporadicName) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hl : ¬ P1ThreeSporList p s) :
    SporMidAt (NativeSporadic.Carrier s) p := by
  by_cases h3 : p ^ 3 ∣ Nat.card (NativeSporadic.Carrier s)
  · rw [hcard s] at h3
    rcases offList_cases s p hp hp2 h3 with h | h
    · exact absurd h hl
    · unfold P1OffRow at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      exacts [sporMidAt_M12_three, sporMidAt_M24_three, sporMidAt_J2_three, sporMidAt_J4_three,
        sporMidAt_J4_eleven, sporMidAt_HS_five, sporMidAt_He_three, sporMidAt_He_seven,
        sporMidAt_Ru_three, sporMidAt_Ru_five, sporMidAt_McL_five, sporMidAt_Co2_five,
        sporMidAt_Co3_five, sporMidAt_Th_five, sporMidAt_ON_seven]
  · exact Or.inl h3

section Final


theorem kFactP1ThreeSpor_of
    (hbr : ∀ s : TauCeti.SporadicName,
      Nonempty (NativeSporadic.Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (hOutS : ∀ s : TauCeti.SporadicName, ∀ p : ℕ, p.Prime → p ≠ 2 →
      ¬ p ∣ Nat.card (ComponentClassification.OuterAutomorphisms.Outer
        (TauCeti.CFSGIndex.sporadic s).Group))
    (hMcard : Nat.card Open.MonsterY443Derived = Open.monsterOrder) : KFactP1ThreeSpor :=
  kFactP1ThreeSpor_of_midAt hbr hOutS fun s p _ hp2 hl =>
    sporMidAt_of_offList (card_carrier_eq_sporOrd hMcard) s p Fact.out hp2 hl

end Final

end CFSG.AGLEmbedding
