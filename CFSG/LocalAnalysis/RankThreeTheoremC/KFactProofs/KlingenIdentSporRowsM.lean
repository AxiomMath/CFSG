module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentSporAux
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.FiveTorusMonster
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.SevenMonster
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.OrdinaryProofs.SevenTCGenWeakCore
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.OrdinaryProofs.MonsterThirteenCubic

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentSporAux

open CFSG.Open CFSG.Blueprint CFSG.AGLEmbedding


theorem weakCore_eq_top_M_three {K : Type} [Group K] [Finite K]
    [Nontrivial (K ⧸ Subgroup.center K)] (e : K ⧸ Subgroup.center K ≃* NativeSporadic.Carrier .M)
    (hZ : IsPGroup 3 (Subgroup.center K)) (T : Sylow 3 K) :
    GLBWeakCore 3 (T : Subgroup K) = ⊤ :=
  weakCore_eq_top_of_normalizerGen
    (CFSG.AGLEmbedding.MonsterThree.liftableNormalizerGen_M e.injective.nontrivial) e hZ T

theorem genData_M_five {T : Type} [Group T] [Finite T] [IsSimpleGroup T] [Fact (Nat.Prime 5)]
    (e : T ≃* NativeSporadic.Carrier .M) : GenData T 5 :=
  ⟨CFSG.AGLEmbedding.Norton.MON5_7.weakCore_five_of_monster e,
    CFSG.AGLEmbedding.Norton.MON5_7.coverWeakGen_five_of_monster e⟩

theorem genData_M_seven {T : Type} [Group T] [Finite T] [IsSimpleGroup T] [Fact (Nat.Prime 7)]
    (e : T ≃* NativeSporadic.Carrier .M) : GenData T 7 := by
  obtain ⟨ε⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple e
  haveI : Finite ↥CFSG.Monster.Generated.Gmat := Finite.of_equiv T ε.toEquiv
  exact ⟨fun S => CFSG.AGLEmbedding.Norton.OrdinaryProofs.weakCore_seven_of_tcGen ε
      CFSG.AGLEmbedding.Norton.MON5_7.tcGenDatum_seven_gmat S,
    CFSG.AGLEmbedding.Norton.MON5_7.coverWeakGen_seven_of_monster e⟩

theorem rankData_M_thirteen {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    [Fact (Nat.Prime 13)] (e : T ≃* NativeSporadic.Carrier .M) : RankData T 13 := by
  have hcard : Nat.card T = monsterOrder :=
    CFSG.AGLEmbedding.MonsterRows.card_eq_monsterOrder CFSG.Open.Open.monster_y443_derived_card e
  have hS : ¬ 13 ^ 4 ∣ Nat.card T := by
    rw [hcard]
    norm_num [monsterOrder]
  obtain ⟨ε⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple e
  exact Or.inr ⟨hS, CFSG.AGLEmbedding.Norton.MON11_13.hasNoncommPair_thirteen_of_mulEquiv_Gmat ε,
    CFSG.AGLEmbedding.Norton.OrdinaryProofs.kernelTrivialAt_thirteen_of_mulEquiv_Gmat ε hS⟩

theorem not_dvd_card_outer_M {T : Type} [Group T] [IsSimpleGroup T]
    (e : T ≃* NativeSporadic.Carrier .M) {p : ℕ} (hp : p.Prime) :
    ¬ p ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer T) := by
  rw [CFSG.RankThree.PartOne.SPOR.card_outer_M_of_simple e]
  exact fun h => hp.one_lt.ne' (Nat.dvd_one.mp h)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentSporAux
