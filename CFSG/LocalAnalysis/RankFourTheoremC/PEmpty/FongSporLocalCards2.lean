module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Classification
public import CFSG.Sporadic.Bridge.J2
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.Bridge.HeSurj
public import CFSG.Sporadic.Bridge.SuzSurj
public import CFSG.Sporadic.Presentation.Co2Exact

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

theorem hcard_J2 :
    ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A),
      Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic .J2).Group) → Nat.card L = 604800 := by
  intro A _ _ L ⟨e⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J2.nonempty_mulEquiv
  rw [Nat.card_congr (e.trans b.symm).toEquiv]
  exact CFSG.Sporadic.J2.card_J2

theorem hcard_He :
    ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A),
      Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic .He).Group) → Nat.card L = 4030387200 := by
  intro A _ _ L ⟨e⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
  rw [Nat.card_congr (e.trans b.symm).toEquiv]
  exact CFSG.Sporadic.He.card_He

theorem hcard_Suz :
    ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A),
      Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic .Suz).Group) → Nat.card L = 448345497600 := by
  intro A _ _ L ⟨e⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Suz.nonempty_mulEquiv
  rw [Nat.card_congr (e.trans b.symm).toEquiv]
  exact CFSG.Sporadic.Suz.card_Suz

theorem hcard_Co2 :
    ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A),
      Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic .Co2).Group) → Nat.card L = 42305421312000 := by
  intro A _ _ L ⟨e⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co2.nonempty_mulEquiv
  rw [Nat.card_congr (e.trans b.symm).toEquiv]
  exact CFSG.Sporadic.Co2.card_Co2

theorem prime_dvd_of_orderOf {A : Type} [Group A] [Finite A] (L : Subgroup A) {z : A}
    (hzL : z ∈ L) {p : ℕ} (hz : orderOf z = p) : p ∣ Nat.card L := by
  have h := orderOf_dvd_natCard (⟨z, hzL⟩ : ↥L)
  rw [Subgroup.orderOf_mk, hz] at h
  exact h

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

end
