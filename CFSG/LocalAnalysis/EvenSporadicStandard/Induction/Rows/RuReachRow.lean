module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuReach
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuThm54ReachHered
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction.Hyp
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog

@[expose] def RuSuzukiModel : Prop :=
  ∀ (G : Type) [Group G] (L K : Subgroup G) (u : G), IsSporadic ↥L .Ru → RuPair G L K u →
    SuzukiModel ↥K 2 3

structure RuFamilyFacts : Prop where
  not_exc : ∀ (X : Type) [Group X], Sol78Thm54Types X → NotExc X
  cover_rank : ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X →
    Sol78Thm54Types (X ⧸ center X) → 3 ≤ CFSG.pRank 2 X

section RuReachRow

theorem ru_pinned_card (Y : Type) [Group Y] (h : IsSporadic Y .Ru) :
    Nat.card Y = 145926144000 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact card_carrier_ru

theorem dvd29_card_ru (Y : Type) [Group Y] (h : IsSporadic Y .Ru) : 29 ∣ Nat.card Y := by
  rw [ru_pinned_card Y h]
  norm_num

theorem ru_fi23 : Fi23Excl .Ru :=
  fi23Excl_of_card (n := 145926144000) ru_pinned_card (by norm_num)

theorem ru_sp_not_exc : SporadicNotExc .Ru :=
  sporadicNotExc_of_card (N := 145926144000) (c := 6633) ru_pinned_card (by norm_num)
    (by norm_num) (by norm_num)

attribute [local irreducible] CFSG.Blueprint.NativeSporadic.carrierGroup

theorem isKRu_data (hf : RuLocalFacts) (hS : RuSuzukiModel) {X : Type} [Group X] (h : IsKRu X) :
    IsSimpleGroup X ∧ Nat.card X = 29120 ∧ SuzukiModel X 2 3 ∧ CFSG.IsQuasisimple X := by
  obtain ⟨u, K, hQ, ⟨e⟩⟩ := h
  have hs := ruPinned_simple hf hQ
  have hcard : Nat.card X = 29120 := by
    rw [Nat.card_congr e.toEquiv]
    exact hQ.2.2.2.2
  have hsX : IsSimpleGroup X := @MulEquiv.isSimpleGroup _ _ _ _ hs e
  have : Finite X := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hna : ∃ a b : X, a * b ≠ b * a := not_comm_of_simple_not_prime (by rw [hcard]; norm_num)
  exact ⟨hsX, hcard, suzukiModel_of_mulEquiv' e.symm (hS (Carrier .Ru) ⊤ K u ru_top_sporadic hQ),
    isQuasisimple_of_simple_nonabelian hsX hna⟩

theorem isKRu_iso (hf : RuLocalFacts) (hS : RuSuzukiModel) {X Y : Type} [Group X] [Group Y]
    (hX : IsKRu X) (hY : IsKRu Y) : Nonempty (X ≃* Y) := by
  obtain ⟨-, -, hSX, -⟩ := isKRu_data hf hS hX
  obtain ⟨-, -, hSY, -⟩ := isKRu_data hf hS hY
  obtain ⟨eX⟩ := CFSG.LieType.Multipliers.Sz8.nonempty_mulEquiv_suzukiGroup_of_blueprint
    (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hSX⟩)))
  obtain ⟨eY⟩ := CFSG.LieType.Multipliers.Sz8.nonempty_mulEquiv_suzukiGroup_of_blueprint
    (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hSY⟩)))
  exact ⟨eX.trans eY.symm⟩

theorem isKRu_oddCore (hf : RuLocalFacts) (hS : RuSuzukiModel) {X : Type} [Group X]
    (h : IsKRu X) : CFSG.oddCore X = ⊥ := by
  obtain ⟨hs, hc, -, -⟩ := isKRu_data hf hS h
  have : Finite X := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  exact oddCore_eq_bot_of_isSimpleGroup (by rw [hc]; decide)

theorem isKRu_known (hf : RuLocalFacts) (hS : RuSuzukiModel) {X : Type} [Group X] (h : IsKRu X) :
    Sol78Thm54Types (X ⧸ center X) ∧ Nat.card (X ⧸ center X) = 29120 := by
  obtain ⟨hs, hc, hSX, hq⟩ := isKRu_data hf hS h
  have hZ := center_eq_bot_of_simple_isQuasisimple_row hq
  let e : X ⧸ center X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨Or.inl ⟨1, le_rfl, suzukiModel_of_mulEquiv' e.symm hSX⟩, ?_⟩
  rw [Nat.card_congr e.toEquiv]
  exact hc

theorem ru_notR {Y : Type} [Group Y] [Finite Y] {N : Subgroup Y} (hN : FStarSimple N)
    (hidx : N.index ≤ 2) {L : Subgroup Y} (hL : InL L) (hcov : OddCover .Ru L)
    (hR : IsSporadic ↥N .Ru ∨ (Sol78Thm54Types ↥N ∧ ¬ 29 ∣ Nat.card ↥N)) : False := by
  have : N.Normal := hN.normal
  have hLN : L ≤ N := le_of_perfect_of_index_le_two hidx hcov.1.1
  have hne : L ≠ N := inL_ne_of_fStarSimple hN hL
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥L)
  have h2 := ru_pinned_card _ hcov.2.2
  have h3 : 0 < Nat.card ↥(center ↥L) := hcov.2.1.pos
  rw [h2] at h1
  rcases hR with hRu | ⟨-, h29N⟩
  · have h5 := ru_pinned_card _ hRu
    have h6 : 145926144000 ≤ Nat.card ↥L := by rw [h1]; exact Nat.le_mul_of_pos_right _ h3
    have h4 : Nat.card ↥L ≤ Nat.card ↥N := Subgroup.card_le_of_le hLN
    exact hne (Subgroup.eq_of_le_of_card_ge hLN (by omega))
  · have h29L : 29 ∣ Nat.card ↥L := by
      rw [h1]
      exact Dvd.dvd.mul_right (by norm_num) _
    exact h29N (h29L.trans (Subgroup.card_dvd_of_le hLN))

theorem ru_closure {Y : Type} [Group Y] [Finite Y] (h54 : Sol78Thm54ReachAt Y)
    {N' : Subgroup Y} (hN : FStarSimple N') (hidx : N'.index ≤ 2)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog Y) {P : Subgroup Y} (hP : SolStd P)
    (hPq : CFSG.IsQuasisimple ↥P)
    (hR : IsSporadic (↥P ⧸ center ↥P) .Ru ∨ (Sol78Thm54Types (↥P ⧸ center ↥P) ∧
      ¬ 29 ∣ Nat.card (↥P ⧸ center ↥P)))
    (hns : ¬ IsSporadic (↥P ⧸ center ↥P) .Ru) :
    IsSporadic ↥N' .Ru ∨ (Sol78Thm54Types ↥N' ∧ ¬ 29 ∣ Nat.card ↥N') := by
  rcases hR with hRu | ⟨hT, h29⟩
  · exact absurd hRu hns
  · rcases h54 N' hN hidx hkp P hP hPq hT h29 with ⟨hT', h29'⟩ | ⟨-, hRu⟩
    · exact Or.inr ⟨hT', h29'⟩
    · exact Or.inl hRu

theorem ru_pair_into {Y : Type} [Group Y] [Finite Y] (h54 : Sol78Thm54ReachAt Y)
    (hf : RuLocalFacts) (hS : RuSuzukiModel) {N' : Subgroup Y} (hN : FStarSimple N')
    (hidx : N'.index ≤ 2)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog Y) {P : Subgroup Y} (hP : SolStd P)
    (hPq : CFSG.IsQuasisimple ↥P)
    (hR : IsSporadic (↥P ⧸ center ↥P) .Ru ∨ (Sol78Thm54Types (↥P ⧸ center ↥P) ∧
      ¬ 29 ∣ Nat.card (↥P ⧸ center ↥P)))
    (hns : ¬ IsSporadic (↥P ⧸ center ↥P) .Ru) (hN' : IsSporadic ↥N' .Ru) :
    IsKRu (↥P ⧸ CFSG.oddCore ↥P) := by
  rcases hR with hRu | ⟨hT, h29⟩
  · exact absurd hRu hns
  · rcases h54 N' hN hidx hkp P hP hPq hT h29 with ⟨hT', h29'⟩ | ⟨hSz, -⟩
    · exact absurd (dvd29_card_ru ↥N' hN') h29'
    · obtain ⟨K, u, hQ⟩ := hf.exists_pair (Carrier .Ru) ⊤ ru_top_sporadic
      obtain ⟨eP⟩ := CFSG.LieType.Multipliers.Sz8.nonempty_mulEquiv_suzukiGroup_of_blueprint
        (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hSz⟩)) : LieModel ↥P .twistedB2 0 2 3)
      obtain ⟨eK⟩ := CFSG.LieType.Multipliers.Sz8.nonempty_mulEquiv_suzukiGroup_of_blueprint
        (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hS (Carrier .Ru) ⊤ K u ru_top_sporadic hQ⟩)) :
          LieModel ↥K .twistedB2 0 2 3)
      have hK : IsKRu ↥P := ⟨u, K, hQ, ⟨eP.trans eK.symm⟩⟩
      exact isKPinned_isoInv .Ru _ ↥P (↥P ⧸ CFSG.oddCore ↥P)
        (quotientOddCoreEquiv (isKRu_oddCore hf hS hK)).symm hK

theorem isKRu_suzuki_cq (hf : RuLocalFacts) (hS : RuSuzukiModel) {X : Type} [Group X]
    (h : IsKRu X) : SuzukiModel (X ⧸ center X) 2 3 := by
  obtain ⟨hs, -, hSX, hq⟩ := isKRu_data hf hS h
  have := hs
  have hZ := center_eq_bot_of_simple_isQuasisimple_row hq
  let e : X ⧸ center X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact suzukiModel_of_mulEquiv' e.symm hSX

end RuReachRow

end CFSG.EvenSporadicStandard.Induction
