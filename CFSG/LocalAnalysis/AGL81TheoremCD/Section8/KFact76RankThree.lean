module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.Defs

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section8

@[expose] def KFact76MaxRankThree : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsKGroup Y → CFSG.pPrimeCore 3 Y = ⊥ →
    ∀ A : Subgroup Y, Nat.card A = 3 →
      (∀ g : Y, A.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (A : Set Y) →
        A.map (MulAut.conj g).toMonoidHom = A) →
      CFSG.Open.pRank 3 (Subgroup.normalClosure (A : Set Y)) ≤ 3 →
      IsSimpleGroup ↥(Subgroup.normalClosure (A : Set Y)) ∧
        (CFSG.Open.pRank 3 (Subgroup.normalClosure (A : Set Y)) = 1 ∨
          ∀ W : Subgroup Y,
            Subgroup.normalizer (A : Set Y) ⊓ Subgroup.normalClosure (A : Set Y) ≤ W →
            W ≤ Subgroup.normalClosure (A : Set Y) →
            W = Subgroup.normalizer (A : Set Y) ⊓ Subgroup.normalClosure (A : Set Y) ∨
              W = Subgroup.normalClosure (A : Set Y))

theorem kFact76MaxRankThree_of_kFact76Max (h : KFact76Max) : KFact76MaxRankThree :=
  fun Y _ _ hK hc A hA hwc _ => h Y hK hc A hA hwc

end CFSG.LocalAnalysis.AGL81TheoremCD.Section8
