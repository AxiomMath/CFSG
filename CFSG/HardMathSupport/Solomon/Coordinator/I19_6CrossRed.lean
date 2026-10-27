module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10Red

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.HardMathSupport.Timmesfeld.CrossChar

set_option linter.unusedSectionVars false

@[expose] def LocalTwoCrossFam (p : ℕ) (k : LieFamily) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, k.Matches idx.1 →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) → idx.1.characteristic ≠ p →
        (∀ idx' : TauCeti.ValidLieTypeIndex, IsLpEpsIndex p idx'.1 →
          IsEmpty (S ≃* (TauCeti.CFSGIndex.lie idx').Group)) → IsLocallyBalancedAbs p 2 S

@[expose] def LocalTwoCrossFamCat (p : ℕ) (k : LieFamily) : Prop :=
  ∀ idx : TauCeti.ValidLieTypeIndex, k.Matches idx.1 → idx.1.characteristic ≠ p →
    (∀ idx' : TauCeti.ValidLieTypeIndex, IsLpEpsIndex p idx'.1 →
      IsEmpty (Cat idx ≃* (TauCeti.CFSGIndex.lie idx').Group)) →
    IsLocallyBalancedAbs p 2 (Cat idx)

theorem LocalTwoCrossFam.of_cat {p : ℕ} {k : LieFamily} (h : LocalTwoCrossFamCat p k) :
    LocalTwoCrossFam p k := by
  intro S _ _ _ _ idx hk ⟨e⟩ hc hnexc
  exact IsLocallyBalancedAbs.of_mulEquiv e (h idx hk hc fun idx' hidx' =>
    ⟨fun f => (hnexc idx' hidx').false (e.trans f)⟩)

theorem localTwoBalanceCrossCharThree_of_families (h : ∀ k, LocalTwoCrossFam 3 k) :
    LocalTwoBalanceCrossCharThree := by
  intro S _ _ hS hnab idx hidx hc hnexc
  obtain ⟨k, hk⟩ := exists_lieFamily idx.1
  exact h k S hS hnab idx hk hidx hc hnexc

theorem localTwoBalanceCrossCharFive_of_families (h : ∀ k, LocalTwoCrossFam 5 k) :
    LocalTwoBalanceCrossCharFive := by
  intro S _ _ hS hnab idx hidx hc hnexc
  obtain ⟨k, hk⟩ := exists_lieFamily idx.1
  exact h k S hS hnab idx hk hidx hc hnexc

end CFSG.HardMathSupport.Solomon.Coordinator
