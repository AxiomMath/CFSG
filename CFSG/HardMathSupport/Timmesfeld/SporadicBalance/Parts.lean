module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Reduction
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicOne

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.Open CFSG.Blueprint

@[expose] def SporadicOPrimeHolds (name : TauCeti.SporadicName) (p : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S],
    Nonempty (S ≃* NativeSporadic.Carrier name) →
    OPrimeCoreTrivialAt p S

@[expose] def SporadicOuterHolds (name : TauCeti.SporadicName) (p : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S],
    Nonempty (S ≃* NativeSporadic.Carrier name) →
    NoOuterFixesCentralizer p S

@[expose] def SporadicOnePairHolds (name : TauCeti.SporadicName) (p : ℕ) : Prop :=
  SporadicOPrimeHolds name p ∧ SporadicOuterHolds name p

structure SporadicOneParts : Prop where
  J3_three : SporadicOnePairHolds .J3 3
  McL_three : SporadicOnePairHolds .McL 3
  Suz_three : SporadicOnePairHolds .Suz 3
  ONan_three : SporadicOnePairHolds .ONan 3
  Co3_three : SporadicOnePairHolds .Co3 3
  Co2_three : SporadicOnePairHolds .Co2 3
  Co1_three : SporadicOnePairHolds .Co1 3
  Fi22_three : SporadicOnePairHolds .Fi22 3
  Fi23_three : SporadicOnePairHolds .Fi23 3
  Fi24Prime_three : SporadicOnePairHolds .Fi24Prime 3
  HN_three : SporadicOnePairHolds .HN 3
  Ly_three : SporadicOnePairHolds .Ly 3
  Th_three : SporadicOnePairHolds .Th 3
  B_three : SporadicOnePairHolds .B 3
  M_three : SporadicOnePairHolds .M 3
  Co1_five : SporadicOnePairHolds .Co1 5
  HN_five : SporadicOnePairHolds .HN 5
  Ly_five : SporadicOnePairHolds .Ly 5
  B_five : SporadicOnePairHolds .B 5
  M_five : SporadicOnePairHolds .M 5
  M_seven : SporadicOnePairHolds .M 7

structure SporadicOneRest : Prop where
  Suz_three : SporadicOnePairHolds .Suz 3
  ONan_three : SporadicOnePairHolds .ONan 3
  Co3_three : SporadicOnePairHolds .Co3 3
  Co2_three : SporadicOnePairHolds .Co2 3
  Co1_three : SporadicOnePairHolds .Co1 3
  Fi22_three : SporadicOnePairHolds .Fi22 3
  Fi23_three : SporadicOnePairHolds .Fi23 3
  Fi24Prime_three : SporadicOnePairHolds .Fi24Prime 3
  HN_three : SporadicOnePairHolds .HN 3
  Ly_three : SporadicOnePairHolds .Ly 3
  Th_three : SporadicOnePairHolds .Th 3
  B_three : SporadicOnePairHolds .B 3
  M_three : SporadicOnePairHolds .M 3
  Co1_five : SporadicOnePairHolds .Co1 5
  HN_five : SporadicOnePairHolds .HN 5
  Ly_five : SporadicOnePairHolds .Ly 5
  B_five : SporadicOnePairHolds .B 5
  M_five : SporadicOnePairHolds .M 5
  M_seven : SporadicOnePairHolds .M 7

theorem SporadicOneRest.toParts (hJ3 : SporadicOnePairHolds .J3 3)
    (hMcL : SporadicOnePairHolds .McL 3) (h : SporadicOneRest) : SporadicOneParts :=
  ⟨hJ3, hMcL, h.Suz_three, h.ONan_three, h.Co3_three, h.Co2_three, h.Co1_three,
    h.Fi22_three, h.Fi23_three, h.Fi24Prime_three, h.HN_three, h.Ly_three, h.Th_three,
    h.B_three, h.M_three, h.Co1_five, h.HN_five, h.Ly_five, h.B_five, h.M_five, h.M_seven⟩

theorem SporadicOneParts.holds (h : SporadicOneParts) (name : TauCeti.SporadicName) (p : ℕ)
    (hp : SporadicOnePair name p) : SporadicOnePairHolds name p := by
  unfold SporadicOnePair at hp
  rcases hp with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, rfl⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    exacts [h.J3_three, h.McL_three, h.Suz_three, h.ONan_three, h.Co3_three, h.Co2_three,
      h.Co1_three, h.Fi22_three, h.Fi23_three, h.Fi24Prime_three, h.HN_three, h.Ly_three,
      h.Th_three, h.B_three, h.M_three]
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl
    exacts [h.Co1_five, h.HN_five, h.Ly_five, h.B_five, h.M_five]
  · exact h.M_seven

theorem sporadicLocalOnePairs_of_parts (hB : SporadicBridges) (hOut : SporadicOuterLeTwo)
    (h : SporadicOneParts) : SporadicLocalOnePairs := by
  intro S _ _ hS hnab name he p hp hpair
  have hp2 : p ≠ 2 := by
    unfold SporadicOnePair at hpair
    rcases hpair with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num
  have hcen : Subgroup.center S = ⊥ := by
    have := hS
    exact center_eq_bot_of_isSimpleGroup hnab
  obtain ⟨h1, h2⟩ := h.holds name p hpair
  have he' : Nonempty (S ≃* NativeSporadic.Carrier name) := ⟨he.some.trans (hB name).some.symm⟩
  have := hS
  replace h1 := h1 S he'
  replace h2 := h2 S he'
  exact isLocallyOneBalancedAbs_of_parts hp hp2 hcen (hOut S hS hnab name he) h1 h2

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
