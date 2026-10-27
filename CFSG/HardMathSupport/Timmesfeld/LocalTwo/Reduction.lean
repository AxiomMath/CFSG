module

public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeReduction
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop21Assembly

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator

@[expose] def IsLpEpsIndex (p : ℕ) (d : TauCeti.LieTypeIndex) : Prop :=
  (∃ Q : TauCeti.PrimePower, d = .A (p - 1) Q ∧ Q.card % p = 1) ∨
  (∃ Q : TauCeti.PrimePower, d = .twistedA (p - 1) Q ∧ (Q.card + 1) % p = 0)

@[expose] def LocalTwoBalanceSimpleGtFive : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    IsCatalogGroup S → (∀ n : ℕ, IsEmpty (S ≃* ↥(alternatingGroup (Fin n)))) →
      ∀ p : ℕ, p.Prime → 5 < p →
        (∀ idx : TauCeti.ValidLieTypeIndex, IsLpEpsIndex p idx.1 →
          IsEmpty (S ≃* (TauCeti.CFSGIndex.lie idx).Group)) → IsLocallyBalancedAbs p 2 S

@[expose] def LocalTwoBalanceAltGtFive : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProper G → ∀ p : ℕ, p.Prime → 5 < p →
    ∀ X : Subgroup G, X ≠ ⊤ → ∀ B : Subgroup G, B ≤ X → IsElemAbelian p B →
      GLATwoLocalRank p ↥X ≤ CFSG.Open.pRank p B → 2 ≤ CFSG.Open.pRank p B →
      ∀ L : Subgroup G, GLAPComponent p X L → ∀ n : ℕ,
        Nonempty ((barOf p L ⧸ Subgroup.center (barOf p L)) ≃* ↥(alternatingGroup (Fin n))) →
          IsCompLocallyBalanced p 2 B L

@[expose] def LocalTwoBalanceLpEpsGtFive : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProper G → ∀ p : ℕ, p.Prime → 5 < p →
    ∀ X : Subgroup G, X ≠ ⊤ → ∀ B : Subgroup G, B ≤ X → IsElemAbelian p B →
      GLATwoLocalRank p ↥X ≤ CFSG.Open.pRank p B → 2 ≤ CFSG.Open.pRank p B →
      ∀ L : Subgroup G, GLAPComponent p X L → ∀ idx : TauCeti.ValidLieTypeIndex,
        IsLpEpsIndex p idx.1 →
        Nonempty ((barOf p L ⧸ Subgroup.center (barOf p L)) ≃*
          (TauCeti.CFSGIndex.lie idx).Group) →
          IsCompLocallyBalanced p 2 B L

theorem localTwoBalanceGtFive_of_parts (hS : LocalTwoBalanceSimpleGtFive)
    (hA : LocalTwoBalanceAltGtFive) (hE : LocalTwoBalanceLpEpsGtFive) :
    LocalTwoBalanceGtFive := by
  intro G _ _ hG p hp hp5 X hX B hBX hB hrank h2 L hL
  obtain ⟨hsimple, hnab, hcat⟩ := isCatalogGroup_quotient_center_barOf hp hG hX hL
  by_cases halt : ∃ n : ℕ,
      Nonempty ((barOf p L ⧸ Subgroup.center (barOf p L)) ≃* ↥(alternatingGroup (Fin n)))
  · obtain ⟨n, hn⟩ := halt
    exact hA G hG p hp hp5 X hX B hBX hB hrank h2 L hL n hn
  · by_cases hexc : ∃ idx : TauCeti.ValidLieTypeIndex, IsLpEpsIndex p idx.1 ∧
        Nonempty ((barOf p L ⧸ Subgroup.center (barOf p L)) ≃*
          (TauCeti.CFSGIndex.lie idx).Group)
    · obtain ⟨idx, hidx, he⟩ := hexc
      exact hE G hG p hp hp5 X hX B hBX hB hrank h2 L hL idx hidx he
    · have hnalt : ∀ n : ℕ,
          IsEmpty ((barOf p L ⧸ Subgroup.center (barOf p L)) ≃* ↥(alternatingGroup (Fin n))) :=
        fun n => not_nonempty_iff.1 fun h => halt ⟨n, h⟩
      have hnexc : ∀ idx : TauCeti.ValidLieTypeIndex, IsLpEpsIndex p idx.1 →
          IsEmpty ((barOf p L ⧸ Subgroup.center (barOf p L)) ≃*
            (TauCeti.CFSGIndex.lie idx).Group) :=
        fun idx hidx => not_nonempty_iff.1 fun h => hexc ⟨idx, hidx, h⟩
      have hperf : commutator (barOf p L) = ⊤ := (isQuasisimple_barOf hp hL).1
      exact (IsLocallyBalancedAbs.of_quotient_center hperf
        (hS _ hsimple hnab hcat hnalt p hp hp5 hnexc)).isLocallyBalanced _

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
