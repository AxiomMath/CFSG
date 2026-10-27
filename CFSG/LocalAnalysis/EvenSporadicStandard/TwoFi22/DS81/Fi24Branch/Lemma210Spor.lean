module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUSporSROrd
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHallTwoArithAltSporSporadic

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.ComponentClassification.GSThmB.QPUSpor (sporOrder sporFactors)

theorem ds81Lemma210_spor
    {Y : Type} [Group Y] [IsSimpleGroup Y] (hs : SporadicRep Y)
    (h19 : 2 ^ 19 ∣ Nat.card Y) (h21 : ¬ 2 ^ 21 ∣ Nat.card Y) : False := by
  obtain ⟨s, ⟨e⟩⟩ := hs
  by_cases hM : s = .M
  · subst hM
    rw [CFSG.SeitzReduction.RankOne.card_of_mulEquiv_nativeM e] at h19 h21
    exact h21 (by norm_num [CFSG.Open.monsterOrder])
  · rw [Nat.card_congr e.toEquiv,
      CFSG.ComponentClassification.GSThmB.QPUSpor.card_carrier_eq_sporOrder s hM] at h19 h21
    cases s <;> first
      | exact absurd rfl hM
      | (simp only [sporOrder, sporFactors] at h19 h21; revert h19 h21; decide)

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
