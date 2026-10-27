module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Alt
public import CFSG.HardMathSupport.Timmesfeld.Tables.Alt.Main
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_RedDefs
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.Tables112Families
public import CFSG.Open.StatedDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Inputs
public import CFSG.LocalAnalysis.GLTheoremB.Prop98Defs
public import CFSG.LocalAnalysis.SectionRank.Alternating
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.theorem_3_4
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.Defs

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Census

open CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Timmesfeld.Coordinator

@[expose] def IsU3TwoPowOdd (G : Type) [Group G] : Prop :=
  ∃ n : ℕ, Odd n ∧ ¬ 3 ∣ n ∧ 1 < n ∧
    CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSU 3 2 n

@[expose] def U3TwoPowOddRankTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsU3TwoPowOdd G → 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G)

@[expose] def LieLocalCensus : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) [Finite (TauCeti.CFSGIndex.lie d).Group],
    3 ∣ Nat.card (TauCeti.CFSGIndex.lie d).Group →
      ThreeTwoWitness (TauCeti.CFSGIndex.lie d).Group ∨
        3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (TauCeti.CFSGIndex.lie d).Group) ∨
          IsL2TwoPowOdd (TauCeti.CFSGIndex.lie d).Group ∨
            IsU3TwoPowOdd (TauCeti.CFSGIndex.lie d).Group

@[expose] def SporadicLocalCensus : Prop :=
  ∀ (s : TauCeti.SporadicName) [Finite (TauCeti.CFSGIndex.sporadic s).Group]
    [Nontrivial (TauCeti.CFSGIndex.sporadic s).Group],
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (TauCeti.CFSGIndex.sporadic s).Group) ∨
      ThreeTwoWitness (TauCeti.CFSGIndex.sporadic s).Group

noncomputable def mulEquivCenterQuotient {L : Type*} [Group L] (h : Subgroup.center L = ⊥) :
    (L ⧸ Subgroup.center L) ≃* L :=
  (QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot

theorem tableL2_of (hS : SporadicLocalCensus) (hL : LieLocalCensus) (hU3 : U3TwoPowOddRankTwo) :
    TableL2 where
  T L _ _ hq hK hZ hm hw := by
    have hZ' : Subgroup.center L = ⊥ := Subgroup.card_eq_one.1 hZ
    have hw' : ¬ ThreeTwoWitness L := glaTwoLocalRank_eq_zero_iff.1 hw
    have hperf : Group.IsPerfect L := ⟨hq.1⟩
    have hsimp : IsSimpleGroup (L ⧸ Subgroup.center L) := hq.2
    have hm3 : 3 ∣ Nat.card L := by
      have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num)
        (⊤ : Subgroup L)
      rw [hm, pow_one] at hE
      exact hE ▸ Subgroup.card_subgroup_dvd_card E
    rcases centralQuotient_family hq hK with ⟨n, ⟨e⟩⟩ | ⟨d, ⟨e⟩⟩ | ⟨s, ⟨e⟩⟩
    · exfalso
      have hn := Tables.Alt.five_le_of_centerQuotient hq.1 e
      by_cases h6 : 6 ≤ n
      · have := Tables.Alt.le_pRank_top hn e Nat.prime_three (by norm_num)
        omega
      · obtain rfl : n = 5 := by omega
        exact hw' (threeTwoWitness_alt_five.of_mulEquiv
          ((mulEquivCenterQuotient hZ').symm.trans e).symm)
    · set e1 : L ≃* (TauCeti.CFSGIndex.lie d).Group := (mulEquivCenterQuotient hZ').symm.trans e
      have h3 : 3 ∣ Nat.card (TauCeti.CFSGIndex.lie d).Group := by
        rw [← Nat.card_congr e1.toEquiv]
        exact hm3
      have hnw : ¬ ThreeTwoWitness (TauCeti.CFSGIndex.lie d).Group := fun h =>
        hw' (h.of_mulEquiv e1.symm)
      have : Finite (TauCeti.CFSGIndex.lie d).Group := Finite.of_equiv L e1.toEquiv
      have hm' : CFSG.Open.pRank 3 (⊤ : Subgroup (TauCeti.CFSGIndex.lie d).Group) = 1 := by
        rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e1]
        exact hm
      rcases hL d h3 with h | h | ⟨n, hn, hn1, ⟨f⟩⟩ | hU
      · exact absurd h hnw
      · omega
      · exact ⟨n, hn, hn1, ⟨e1.trans f⟩⟩
      · exfalso
        have := hU3 _ hU
        omega
    · exfalso
      set e1 : L ≃* (TauCeti.CFSGIndex.sporadic s).Group :=
        (mulEquivCenterQuotient hZ').symm.trans e
      have : Finite (TauCeti.CFSGIndex.sporadic s).Group := Finite.of_equiv L e1.toEquiv
      have : Nontrivial (TauCeti.CFSGIndex.sporadic s).Group := by
        have := hsimp.toNontrivial
        have : Nontrivial L := (QuotientGroup.mk_surjective (s := Subgroup.center L)).nontrivial
        exact e1.injective.nontrivial
      rcases hS s with h | h
      · rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e1] at hm
        omega
      · exact hw' (h.of_mulEquiv e1.symm)

end CFSG.HardMathSupport.Timmesfeld.Tables.Census
