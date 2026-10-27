module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.Families
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.SporadicRank
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.SporadicOrders
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Parts

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Blueprint CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance

@[expose] def SporadicTwoPairHolds (name : TauCeti.SporadicName) (p : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
    Nonempty (S ≃* NativeSporadic.Carrier name) → IsLocallyBalancedAbs p 2 S

structure SporadicTwoRest : Prop where
  He_seven : SporadicTwoPairHolds .He 7
  ONan_seven : SporadicTwoPairHolds .ONan 7
  Fi24Prime_seven : SporadicTwoPairHolds .Fi24Prime 7
  Co1_seven : SporadicTwoPairHolds .Co1 7
  Th_seven : SporadicTwoPairHolds .Th 7
  B_seven : SporadicTwoPairHolds .B 7
  M_seven : SporadicTwoPairHolds .M 7
  J4_eleven : SporadicTwoPairHolds .J4 11
  M_eleven : SporadicTwoPairHolds .M 11
  M_thirteen : SporadicTwoPairHolds .M 13

theorem SporadicTwoRest.holds (h : SporadicTwoRest) (name : TauCeti.SporadicName) (p : ℕ)
    (hp : SporadicTwoPair name p) : SporadicTwoPairHolds name p := by
  unfold SporadicTwoPair at hp
  rcases hp with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, rfl⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h.He_seven, h.ONan_seven, h.Fi24Prime_seven, h.Co1_seven, h.Th_seven, h.B_seven,
      h.M_seven]
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl
    exacts [h.J4_eleven, h.M_eleven]
  · exact h.M_thirteen

theorem sporadicTwoPairHolds_of_onePair (hB : SporadicBridges) (hOut : SporadicOuterLeTwo)
    {name : TauCeti.SporadicName} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : SporadicOnePairHolds name p) : SporadicTwoPairHolds name p := by
  intro S _ _ hS hnab he
  have hcen : Subgroup.center S = ⊥ := center_eq_bot_of_isSimpleGroup hnab
  have he' : Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic name).Group) :=
    ⟨he.some.trans (hB name).some⟩
  have hO := hOut S hS hnab name he'
  exact (isLocallyOneBalancedAbs_of_parts hp hp2 hcen hO (h.1 S he) (h.2 S he)).isLocallyBalancedAbs
    hp (by norm_num)

theorem localTwoBalanceSporadicGtFive_of_rest (hB : SporadicBridges) (hOut : SporadicOuterLeTwo)
    (hord : SporadicTwoOrders) (h : SporadicTwoRest) : LocalTwoBalanceSporadicGtFive := by
  intro S _ _ hS hnab name he p hp hp5
  have hp2 : p ≠ 2 := by omega
  have hcen : Subgroup.center S = ⊥ := center_eq_bot_of_isSimpleGroup hnab
  have hO := hOut S hS hnab name he
  obtain ⟨e⟩ := he
  let f : S ≃* NativeSporadic.Carrier name := e.trans (hB name).some.symm
  by_cases hsq : p ^ 2 ∣ Nat.card S
  · have hq : p ^ 2 ∣ Nat.card (NativeSporadic.Carrier name) := by
      rw [← Nat.card_congr f.toEquiv]
      exact hsq
    exact h.holds name p (hord name p hp hp5 hq) S hnab ⟨f⟩
  · exact isLocallyBalancedAbs_two_of_noElemAbelianSquareAut
      (noElemAbelianSquareAut_of_not_dvd hp hp2 hcen hO hsq)

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
