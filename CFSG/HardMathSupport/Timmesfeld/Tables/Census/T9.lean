module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Lie
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.L2Rank
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.Tables112Lie

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Census

open CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Timmesfeld.Coordinator

@[expose] def U3AutRankLeTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsU3TwoPowOdd G →
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut G)) ≤ 2

theorem t9Lie_holds (hE : ExceptionalLieCensus) (hAut : U3AutRankLeTwo) : T9Lie := by
  intro L _ _ hF hq hK hZ hm hw
  obtain ⟨d, ⟨e⟩⟩ := hF
  have hZ' : Subgroup.center L = ⊥ := Subgroup.card_eq_one.1 hZ
  have hw' : ¬ ThreeTwoWitness L := glaTwoLocalRank_eq_zero_iff.1 hw
  set e1 : L ≃* (TauCeti.CFSGIndex.lie d).Group := (mulEquivCenterQuotient hZ').symm.trans e
  have hfin : Finite (TauCeti.CFSGIndex.lie d).Group := Finite.of_equiv L e1.toEquiv
  have hm3 : 3 ∣ Nat.card L := by
    have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (⊤ : Subgroup L)
    rw [hm] at hE
    exact (dvd_pow_self 3 (by norm_num : (2 : ℕ) ≠ 0)).trans
      (hE ▸ Subgroup.card_subgroup_dvd_card E)
  have h3 : 3 ∣ Nat.card (TauCeti.CFSGIndex.lie d).Group := by
    rw [← Nat.card_congr e1.toEquiv]
    exact hm3
  have hnw : ¬ ThreeTwoWitness (TauCeti.CFSGIndex.lie d).Group := fun h =>
    hw' (h.of_mulEquiv e1.symm)
  have hm' : CFSG.Open.pRank 3 (⊤ : Subgroup (TauCeti.CFSGIndex.lie d).Group) = 2 := by
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e1]
    exact hm
  rcases lieLocalCensus_of (lieModelCensus_of hE) d h3 with h | h | h | h
  · exact absurd h hnw
  · omega
  · have := pRank_three_le_one_of_isL2TwoPowOdd h
    omega
  · have := hAut _ h
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) (MulAut.congr e1)]
    exact this

end CFSG.HardMathSupport.Timmesfeld.Tables.Census
