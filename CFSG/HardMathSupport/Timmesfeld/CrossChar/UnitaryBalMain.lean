module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSUDescent
public import CFSG.HardMathSupport.Solomon.LocalBalance.Balance
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop21
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.Tables112Families
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag Matrix
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.Classical CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Lang.Coordinator

@[expose] def DiagUnitaryBalanceOuter : Prop :=
  ∀ (ℓ f : ℕ) (K : Type) [Field K] (h : UnitaryFieldData ℓ f K), ¬(3 = 3 ∧ ℓ ^ f = 2) →
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ ℓ → p ∣ ℓ ^ f + 1 → p ∣ 3 → ℓ ^ (f / p) = 2 →
    ∀ D : Subgroup (MulAut (primeFormP h (idGram K 3))), IsElemAbelian p D →
      Nat.card D = p ^ 3 → ¬ D ≤ primeFormD h (idGram K 3) →
      ∀ H : Subgroup (MulAut (primeFormP h (idGram K 3))),
        innerAut (primeFormP h (idGram K 3)) ≤ H →
        D ≤ Subgroup.normalizer (H : Set (MulAut (primeFormP h (idGram K 3)))) →
        localDeltaIn p H D = ⊥

end CFSG.HardMathSupport.Timmesfeld.CrossChar
