module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_6CrossRed

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def LocalTwoCrossFamAt (p : ℕ) (k : LieFamily)
    (R : TauCeti.ValidLieTypeIndex → Prop) : Prop :=
  ∀ idx : TauCeti.ValidLieTypeIndex, k.Matches idx.1 → R idx → idx.1.characteristic ≠ p →
    (∀ idx' : TauCeti.ValidLieTypeIndex, IsLpEpsIndex p idx'.1 →
      IsEmpty (Cat idx ≃* (TauCeti.CFSGIndex.lie idx').Group)) →
    IsLocallyBalancedAbs p 2 (Cat idx)

theorem localTwoBalanceCrossChar_three_five_of_cat
    (h3 : ∀ k, LocalTwoCrossFamCat 3 k) (h5 : ∀ k, LocalTwoCrossFamCat 5 k) :
    LocalTwoBalanceCrossCharThree ∧ LocalTwoBalanceCrossCharFive :=
  ⟨localTwoBalanceCrossCharThree_of_families fun k => LocalTwoCrossFam.of_cat (h3 k),
   localTwoBalanceCrossCharFive_of_families fun k => LocalTwoCrossFam.of_cat (h5 k)⟩

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
