module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.OrdinaryProofs.MonsterAssembly
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanMonsterRows

public section

namespace CFSG.AGLEmbedding.Norton.OrdinaryProofs

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP
open CFSG.RankThree.PartOne.CTP.Fus

theorem sporCaseThreePrimeData_of_noncomm13 {X : Type} [Group X] [Finite X]
    (hcard : Nat.card X = monsterOrder) (hpair : HasNoncommPair 13 X)
    (hker : KernelTrivialAt X 13) : SporCaseThreePrimeData X 13 :=
  Or.inr (Or.inl ⟨by rw [hcard]; norm_num [monsterOrder], hpair, hker⟩)

theorem monsterCaseThreeData_of_split
    (hMcard : Nat.card CFSG.Open.MonsterY443Derived = monsterOrder)
    (h3 : ∀ [Finite (CFSG.Blueprint.NativeSporadic.Carrier .M)],
      SporCaseThreePrimeData (CFSG.Blueprint.NativeSporadic.Carrier .M) 3)
    (h5 : ∀ [Finite (CFSG.Blueprint.NativeSporadic.Carrier .M)],
      SporCaseThreePrimeData (CFSG.Blueprint.NativeSporadic.Carrier .M) 5)
    (h7 : ∀ [Finite (CFSG.Blueprint.NativeSporadic.Carrier .M)],
      SporCaseThreePrimeData (CFSG.Blueprint.NativeSporadic.Carrier .M) 7)
    (hpair13 : HasNoncommPair 13 (CFSG.Blueprint.NativeSporadic.Carrier .M))
    (hker13 : KernelTrivialAt (CFSG.Blueprint.NativeSporadic.Carrier .M) 13) :
    MonsterCaseThreeData := by
  have hcard : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M) = monsterOrder :=
    CFSG.AGLEmbedding.MonsterRows.card_eq_monsterOrder hMcard (MulEquiv.refl _)
  have hC : SporadicCaseThreeData (CFSG.Blueprint.NativeSporadic.Carrier .M) :=
    sporadicCaseThreeData_of_monsterPrimes hcard h3 h5 h7
      (sporCaseThreePrimeData_of_noncomm13 hcard hpair13 hker13)
  intro T _ _ _ _ ⟨e⟩
  exact sporadicCaseThreeData_of_mulEquiv e hC

end CFSG.AGLEmbedding.Norton.OrdinaryProofs

end
