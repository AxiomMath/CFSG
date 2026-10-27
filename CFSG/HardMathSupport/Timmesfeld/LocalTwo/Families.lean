module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.Reduction

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator

@[expose] def LocalTwoBalanceDefCharGtFive : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
      ∀ p : ℕ, p.Prime → 5 < p → idx.1.characteristic = p → IsLocallyBalancedAbs p 2 S

@[expose] def LocalTwoBalanceCrossCharGtFive : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
      ∀ p : ℕ, p.Prime → 5 < p → idx.1.characteristic ≠ p →
        (∀ idx' : TauCeti.ValidLieTypeIndex, IsLpEpsIndex p idx'.1 →
          IsEmpty (S ≃* (TauCeti.CFSGIndex.lie idx').Group)) → IsLocallyBalancedAbs p 2 S

@[expose] def LocalTwoBalanceSporadicGtFive : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ name : TauCeti.SporadicName, Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic name).Group) →
      ∀ p : ℕ, p.Prime → 5 < p → IsLocallyBalancedAbs p 2 S

theorem localTwoBalanceSimpleGtFive_of_families (hD : LocalTwoBalanceDefCharGtFive)
    (hC : LocalTwoBalanceCrossCharGtFive) (hSp : LocalTwoBalanceSporadicGtFive) :
    LocalTwoBalanceSimpleGtFive := by
  intro S _ _ hsimple hnab hcat hnalt p hp hp5 hnexc
  obtain ⟨i, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic q hq =>
    exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    apply e.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  | alternating n hn =>
    exact ((hnalt n).false e).elim
  | lie idx =>
    by_cases hch : idx.1.characteristic = p
    · exact hD S hsimple hnab idx ⟨e⟩ p hp hp5 hch
    · exact hC S hsimple hnab idx ⟨e⟩ p hp hp5 hch hnexc
  | sporadic name =>
    exact hSp S hsimple hnab name ⟨e⟩ p hp hp5

theorem localTwoBalanceGtFive_of_families (hD : LocalTwoBalanceDefCharGtFive)
    (hC : LocalTwoBalanceCrossCharGtFive) (hSp : LocalTwoBalanceSporadicGtFive)
    (hA : LocalTwoBalanceAltGtFive) (hE : LocalTwoBalanceLpEpsGtFive) :
    LocalTwoBalanceGtFive :=
  localTwoBalanceGtFive_of_parts (localTwoBalanceSimpleGtFive_of_families hD hC hSp) hA hE

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
