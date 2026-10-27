module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Lemma39
public import CFSG.LocalAnalysis.EvenSporadicStandard.Reduction

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open CFSG.Blueprint.NativeSporadic

@[expose] def Sol78Chain (s : TauCeti.SporadicName) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StdHyp G L → IsSporadic L s →
    ∃ (L' K : Subgroup G) (t u : G), StdHyp G L' ∧ IsSporadic L' s ∧ SolomonHyp G L' K t u

@[expose] def Sol78Chain35 (s : TauCeti.SporadicName)
    (P : ∀ (G : Type) [Group G], Subgroup G → Subgroup G → G → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StdHyp G L → IsSporadic L s →
    ∃ (L' K : Subgroup G) (t u : G), StdHyp G L' ∧ IsSporadic L' s ∧
      SolomonSetting G L' K t u ∧ P G L' K u

@[expose] def Sol78Local39 (s : TauCeti.SporadicName)
    (P : ∀ (G : Type) [Group G], Subgroup G → Subgroup G → G → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L' K : Subgroup G) (t u : G), IsSporadic L' s →
    SolomonSetting G L' K t u → P G L' K u →
      (vPairs L' K u).Nonempty ∧ Sol78Fusion39 L' K u ∧ Sol78Generate L' K u

theorem sol78Chain_of_35 {s : TauCeti.SporadicName}
    {P : ∀ (G : Type) [Group G], Subgroup G → Subgroup G → G → Prop}
    (h35 : Sol78Chain35 s P) (hloc : Sol78Local39 s P) : Sol78Chain s := by
  intro G _ _ L hStd hL
  obtain ⟨L', K, t, u, hStd', hL', hS, hP⟩ := h35 G L hStd hL
  obtain ⟨hne, hfus, hgen⟩ := hloc G L' K t u hL' hS hP
  exact ⟨L', K, t, u, hStd', hL', hS.toHyp hne hfus hgen⟩

end CFSG.EvenSporadicStandard.Solomon78
