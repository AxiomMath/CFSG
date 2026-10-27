module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.OrdinaryProofs.MonsterAssembly
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.MonsterFiveSeven
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanMonsterRows
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanMonsterThreeIdent

public section

namespace CFSG.AGLEmbedding.Norton.OrdinaryProofs

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP
open CFSG.RankThree.PartOne.CTP.Fus

theorem sporadicBetaData_of_monsterPrimes_disj {X : Type} [Group X]
    (hcard : Nat.card X = monsterOrder) (hOut : Nat.card (Outer X) ≤ 2)
    (h3 : FusionGenerationOf X 3) (h5 : FusionGenerationOf X 5)
    (h7 : FusionGenerationOf X 7) (h13 : HasNoncommPair 13 X ∨ FusionGenerationOf X 13) :
    SporadicBetaData X := by
  refine ⟨hOut, fun p hp hp2 => ?_⟩
  rw [hcard]
  by_cases hdvd : p ^ 3 ∣ monsterOrder
  · rcases prime_pow_three_dvd_monsterOrder hp hp2 hdvd with rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inr h3)
    · exact Or.inr (Or.inr h5)
    · exact Or.inr (Or.inr h7)
    · rcases h13 with h | h
      · exact Or.inr (Or.inl ⟨by norm_num [monsterOrder], h⟩)
      · exact Or.inr (Or.inr h)
  · exact Or.inl hdvd

section MON57Certificates

theorem monsterBetaData_of_monster13
    (hMcard : Nat.card CFSG.Open.MonsterY443Derived = monsterOrder)
    (h13 : HasNoncommPair 13 (CFSG.Blueprint.NativeSporadic.Carrier .M) ∨
      FusionGenerationOf (CFSG.Blueprint.NativeSporadic.Carrier .M) 13) :
    MonsterBetaData := by
  intro T _ _ _ _ ⟨e⟩
  have hcardT : Nat.card T = monsterOrder :=
    CFSG.AGLEmbedding.MonsterRows.card_eq_monsterOrder hMcard e
  have hOutT : Nat.card (Outer T) ≤ 2 := by
    have h1 := CFSG.RankThree.PartOne.SPOR.card_outer_M_of_simple e
    omega
  have h13T : HasNoncommPair 13 T ∨ FusionGenerationOf T 13 :=
    h13.imp (fun h => hasNoncommPair_of_mulEquiv e h) (fun h => fusionGenerationOf_of_mulEquiv e.symm h)
  exact sporadicBetaData_of_monsterPrimes_disj hcardT hOutT
    (CFSG.AGLEmbedding.MonsterThree.fusionGenerationOf_of_isSimple_monster e)
    (CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.fusionGenerationOf_Monster_five e)
    (CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.fusionGenerationOf_Monster_seven e) h13T

end MON57Certificates

end CFSG.AGLEmbedding.Norton.OrdinaryProofs

end
