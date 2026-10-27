module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.OrdinaryProofs.MonsterThirteenCubic
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.OrdinaryProofs.MonsterCaseThreeAssembly
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.FiveTorusMonster
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MonsterThreeNoMult
public import CFSG.Sporadic.NativeFinite

public section

namespace CFSG.AGLEmbedding.Norton.OrdinaryProofs

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP
open CFSG.RankThree.PartOne.CTP.Fus
open CFSG.AGLEmbedding.Norton.MON11_13

theorem monsterCaseThreeData_of_five_thirteen
    (h7 : ∀ [Finite (CFSG.Blueprint.NativeSporadic.Carrier .M)],
      SporCaseThreePrimeData (CFSG.Blueprint.NativeSporadic.Carrier .M) 7) :
    MonsterCaseThreeData := by
  have :Finite (CFSG.Blueprint.NativeSporadic.Carrier .M) :=
    CFSG.Sporadic.finite_carrier_M_of_card CFSG.Open.Open.monster_y443_derived_card
  have :IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M) := carrier_M_simple
  have :Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have :Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hMcard : Nat.card CFSG.Open.MonsterY443Derived = monsterOrder :=
    CFSG.Open.Open.monster_y443_derived_card
  have hcard : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M) = monsterOrder :=
    CFSG.AGLEmbedding.MonsterRows.card_eq_monsterOrder hMcard (MulEquiv.refl _)
  have hS : ¬ 13 ^ 4 ∣ Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M) := by
    rw [hcard]; norm_num [monsterOrder]
  obtain ⟨ε⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple
    (T := CFSG.Blueprint.NativeSporadic.Carrier .M) (MulEquiv.refl _)
  have hnc : ∃ a b : CFSG.Blueprint.NativeSporadic.Carrier .M, a * b ≠ b * a := by
    by_contra h
    push Not at h
    have :IsMulCommutative (CFSG.Blueprint.NativeSporadic.Carrier .M) :=
      ⟨⟨fun a b => h a b⟩⟩
    have hp : (Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M)).Prime :=
      Group.is_simple_iff_prime_card.mp inferInstance
    rw [hcard] at hp
    have h2 : 2 ∣ monsterOrder := by norm_num [monsterOrder]
    rcases hp.eq_one_or_self_of_dvd 2 h2 with h1 | h1
    · norm_num at h1
    · norm_num [monsterOrder] at h1
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.Y443.nonempty_mulEquiv
  exact monsterCaseThreeData_of_split hMcard
    (fun [_] => CFSG.AGLEmbedding.Norton.sporCaseThreePrimeData_monster_three_noMult hnc
      ⟨MulEquiv.refl _⟩)
    (fun [_] => Or.inr (Or.inr ⟨MON5_7.weakCoreClause_five_of_monster (MulEquiv.refl _),
      Or.inr (MON5_7.coverWeakGen_five_of_monster (MulEquiv.refl _))⟩))
    (fun [_] => h7)
    (hasNoncommPair_thirteen_of_mulEquiv_Gmat ε)
    (kernelTrivialAt_thirteen_of_mulEquiv_Gmat ε hS)

end CFSG.AGLEmbedding.Norton.OrdinaryProofs

end
