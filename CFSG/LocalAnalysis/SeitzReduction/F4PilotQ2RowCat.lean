module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2RowKinds

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.LieType.Ree (ReeTag)

section Cat

@[expose] def TwoRowsCatInput : Prop :=
  Sp6CatalogueClauses → TwoRowsInput

end Cat

section HR8

theorem exists_twoKindAt_of_cat (hcat : Sp6CatalogueClauses) {G : Type} [Group G] [Finite G]
    {L : Subgroup G} {K : Type} [Field K] {t : G} (hw : F4Work L K t 1)
    (e : L ≃* adjointGroup .F4 K) {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = 3) : ∃ κ : Sp6Kind, TwoKindAt e t X₀ κ := by
  have hK2 : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  have hX₀' : Nat.card X₀ = Nat.card K + 1 := by rw [hX₀, hK2]
  have htX : t ∈ centralizer (subgroupToG e X₀ : Set G) :=
    centralizer_le (map_subtype_le _) hw.mem_centralizer
  have hnn := not_normal_map_oddCore_nonsplit_of_card_eq_two hw.standard hK2 e hw.orderOf_eq
    hw.inf_eq hXJ hX₀ rfl rfl
  have hNO := neighbour_overgroup_nonsplit_of_not_normal hcat hw.standard hw.card_eq e
    hw.orderOf_eq hw.inf_eq hXJ hcyc hX₀' rfl htX rfl hnn
  obtain ⟨κ, hκ⟩ := exists_neighbourOvergroupKind hNO
  exact ⟨κ, htX, hκ⟩

@[expose] def TwoKindPairInput (κ κ' : Sp6Kind) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (e : L ≃* adjointGroup .F4 K) (t : G), F4Work L K t 1 →
    ∀ X₀ : Subgroup (adjointGroup .F4 K),
      X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K) → IsCyclic X₀ →
      Nat.card X₀ = 3 → TwoKindAt e t X₀ κ →
      TwoKindAt (e.trans (graphAutF4 K).symm) t X₀ κ' → False

theorem twoRowsCatInput_of_pairs (h : ∀ κ κ', TwoKindPairInput κ κ') : TwoRowsCatInput := by
  intro hcat G _ _ L K _ _ _ e t hw X₀ hXJ hcyc hX₀ htX κ hk
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  obtain ⟨κ', hκ'⟩ := exists_twoKindAt_of_cat hcat hw (e.trans (graphAutF4 K).symm) hXJ hcyc hX₀
  exact h κ κ' G L K e t hw X₀ hXJ hcyc hX₀ ⟨htX, hk⟩ hκ'

@[expose] def consistentKindPairsTwo : List (Sp6Kind × Sp6Kind) :=
  [(.field, .field), (.swap, .swap), (.linear6, .omegaMinus8), (.omegaMinus8, .linear6),
    (.unitary6, .omegaPlus8), (.omegaPlus8, .unitary6)]

@[expose] def TwoMismatchInput : Prop :=
  ∀ κ κ' : Sp6Kind, (κ, κ') ∉ consistentKindPairsTwo → TwoKindPairInput κ κ'

@[expose] def TwoFieldPairInput : Prop :=
  TwoKindPairInput .field .field

@[expose] def TwoSwapPairInput : Prop :=
  TwoKindPairInput .swap .swap

@[expose] def TwoE6PairInput : Prop :=
  TwoKindPairInput .linear6 .omegaMinus8 ∧ TwoKindPairInput .omegaMinus8 .linear6

@[expose] def TwoTwistedE6PairInput : Prop :=
  TwoKindPairInput .unitary6 .omegaPlus8 ∧ TwoKindPairInput .omegaPlus8 .unitary6

theorem twoRowsCatInput_of_pairRows (hM : TwoMismatchInput) (hF : TwoFieldPairInput)
    (hS : TwoSwapPairInput) (hE : TwoE6PairInput) (hT : TwoTwistedE6PairInput) :
    TwoRowsCatInput := by
  refine twoRowsCatInput_of_pairs fun κ κ' => ?_
  cases κ <;> cases κ' <;>
    first
    | exact hF
    | exact hS
    | exact hE.1
    | exact hE.2
    | exact hT.1
    | exact hT.2
    | exact hM _ _ (by decide)

end HR8

end CFSG.SeitzReduction.F4Pilot
