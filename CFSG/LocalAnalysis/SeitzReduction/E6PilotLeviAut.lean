module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviAutPSL
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviAutSp
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatTypeDet

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem rootPerpLevi_single_zero_eq_map_a5Levi :
    EPilot.rootPerpLevi .E6 K (Pi.single (0 : Fin 6) 1) =
      (a5Levi K).map (MulAut.conj (e6RepConj K 0)).toMonoidHom := by
  rw [← range_xLeviHom, xLeviHom, MonoidHom.range_comp, range_slToAdjointE6]

variable (K) in
@[expose] noncomputable def a5LeviEquivXLevi :
    a5Levi K ≃* EPilot.rootPerpLevi .E6 K (Pi.single (0 : Fin 6) 1) :=
  ((a5Levi K).equivMapOfInjective _ (MulAut.conj (e6RepConj K 0)).injective).trans
    (MulEquiv.subgroupCongr rootPerpLevi_single_zero_eq_map_a5Levi.symm)

theorem isSimpleGroup_rootPerpLevi_single_zero :
    IsSimpleGroup (EPilot.rootPerpLevi .E6 K (Pi.single (0 : Fin 6) 1)) := by
  have := isSimpleGroup_a5Levi (K := K)
  exact (a5LeviEquivXLevi K).symm.isSimpleGroup

theorem lieModel_rootPerpLevi_single_zero {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    LieModel (EPilot.rootPerpLevi .E6 K (Pi.single (0 : Fin 6) 1)) .PSL 6 2 f :=
  CFSG.LieType.CurtisTits.lieModel_of_mulEquiv (a5LeviEquivXLevi K) (lieModel_a5Levi hK)

theorem card_rootPerpLevi_single_zero {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    Nat.card (EPilot.rootPerpLevi .E6 K (Pi.single (0 : Fin 6) 1)) = CFSG.Open.ordA 5 (2 ^ f) :=
  F4Pilot.card_eq_evenLieOrder_of_mem_classicalTags (by decide)
    (lieModel_rootPerpLevi_single_zero hK)

theorem card_yLevi {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    Nat.card (yLevi K) = CFSG.Open.ordBC 3 (2 ^ f) :=
  F4Pilot.card_eq_evenLieOrder_of_mem_classicalTags (by decide) (lieModel_yLevi hK)

theorem card_rootPerpLevi_single_zero_ne_card_yLevi :
    Nat.card (EPilot.rootPerpLevi .E6 K (Pi.single (0 : Fin 6) 1)) ≠ Nat.card (yLevi K) := by
  obtain ⟨f, hf, hK⟩ := exists_card_eq_two_pow_eClasses K
  rw [card_rootPerpLevi_single_zero hK, card_yLevi hK]
  exact (F4Pilot.ordBC_ne_ordA_five (n := 3) (by norm_num) hf hf).symm

theorem highRootSL2_subgroupOf_ne_bot :
    (EPilot.highRootSL2 .E6 K).subgroupOf (adjointGroup .E6 K) ≠ ⊥ := by
  intro h
  have h1 : EPilot.highRootSL2 .E6 K = ⊥ := by
    have := congrArg (Subgroup.map (adjointGroup .E6 K).subtype) h
    rwa [subgroupOf_map_subtype, inf_of_le_left EPilot.highRootSL2_le_adjointGroup,
      Subgroup.map_bot] at this
  have h2 : rootSubgroup .E6 K (highRoot .E6) = ⊥ :=
    eq_bot_iff.2 (h1 ▸ EPilot.rootSubgroup_highRoot_le_highRootSL2)
  have : Nontrivial (rootSubgroup .E6 K (highRoot .E6)) :=
    (rootSubgroupEquiv .E6 K (highRoot .E6)).symm.toEquiv.nontrivial
  exact (Subgroup.nontrivial_iff_ne_bot _).1 this h2

theorem factF5_E6 {M : Fin 3 → Subgroup (adjointGroup .E6 K)}
    (hM0 : M 0 = EPilot.rootPerpLevi .E6 K (Pi.single (0 : Fin 6) 1)) (hM1 : M 1 = yLevi K)
    (hM2 : IsSimpleCentralizingFactor (M 2)
      ((EPilot.highRootSL2 .E6 K).subgroupOf (adjointGroup .E6 K)))
    (κ κ' : Fin 3) (ι : M κ ≃* M κ') :
    κ = κ' ∧ ∃ m ∈ M κ',
      ((((EPilot.highRootSL2 .E6 K).subgroupOf (adjointGroup .E6 K)).subgroupOf (M κ)).map
          ι.toMonoidHom).map (M κ').subtype =
        ((EPilot.highRootSL2 .E6 K).subgroupOf (adjointGroup .E6 K)).map
          (MulAut.conj m).toMonoidHom := by
  set J := (EPilot.highRootSL2 .E6 K).subgroupOf (adjointGroup .E6 K) with hJ
  have hS0 : IsSimpleGroup (M 0) := hM0 ▸ isSimpleGroup_rootPerpLevi_single_zero
  have hS1 : IsSimpleGroup (M 1) := hM1 ▸ isSimpleGroup_yLevi
  have hS2 : ¬ IsSimpleGroup (M 2) :=
    not_isSimpleGroup_of_isSimpleCentralizingFactor hM2 highRootSL2_subgroupOf_ne_bot
  have hc01 : Nat.card (M 0) ≠ Nat.card (M 1) := by
    rw [hM0, hM1]
    exact card_rootPerpLevi_single_zero_ne_card_yLevi
  have hA : ∀ k : Fin 3, IsAutConjIn (M k) J := by
    intro k
    match k with
    | 0 => rw [hM0]; exact isAutConjIn_rootPerpLevi_highRootSL2
    | 1 => rw [hM1]; exact isAutConjIn_yLevi_highRootSL2
    | 2 => exact isAutConjIn_of_isSimpleCentralizingFactor hM2
  have hκ : κ = κ' := by
    have hcard : Nat.card (M κ) = Nat.card (M κ') := Nat.card_congr ι.toEquiv
    have hsimp : IsSimpleGroup (M κ) ↔ IsSimpleGroup (M κ') :=
      ⟨fun h => ι.symm.isSimpleGroup, fun h => ι.isSimpleGroup⟩
    match κ, κ' with
    | 0, 0 => rfl
    | 1, 1 => rfl
    | 2, 2 => rfl
    | 0, 1 => exact absurd hcard hc01
    | 1, 0 => exact absurd hcard.symm hc01
    | 0, 2 => exact absurd (hsimp.1 hS0) hS2
    | 2, 0 => exact absurd (hsimp.2 hS0) hS2
    | 1, 2 => exact absurd (hsimp.1 hS1) hS2
    | 2, 1 => exact absurd (hsimp.2 hS1) hS2
  subst hκ
  exact ⟨rfl, hA κ ι⟩

end CFSG.SeitzReduction.E6Pilot
