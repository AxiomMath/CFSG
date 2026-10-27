module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2RowSwapParam
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2PairTables
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2SwapChainModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie CFSG.Assembly.LowTwoRank
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect)
open CFSG.SeitzReduction.SeitzQ2 (SwapParam)
open CFSG.SeitzReduction.SymplecticPilot (nsTorusSp complSp spBlock)

section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem card_perfectCore_complSp_zero_two (hK : Nat.card K = 2) :
    Nat.card (perfectCore (complSp K (0 : Fin 3))) = 360 := by
  have hN : (({0}ᶜ : Finset (Fin 3))).card = 2 := by decide
  have hsp : spBlock K ({0}ᶜ : Finset (Fin 3)) = complSp K (0 : Fin 3) :=
    SymplecticPilot.spBlock_compl_singleton 0
  obtain ⟨-, -, hle⟩ := SymplecticPilot.perfectCore_spBlock_of_card_two hK (N := {0}ᶜ)
    (by rw [hN])
  rw [hsp] at hle
  set H := complSp K (0 : Fin 3) with hHdef
  obtain ⟨e6⟩ := SymplecticPilot.nonempty_statedSp_mulEquiv_perm_of_eq hK hN
  have eH : H ≃* Equiv.Perm (Fin 6) :=
    ((MulEquiv.subgroupCongr hsp).symm.trans
      (SymplecticPilot.spBlockEquiv ({0}ᶜ : Finset (Fin 3))).symm).trans e6
  obtain ⟨ψ⟩ := CFSG.RankThree.CASymplecticSubfield.nonempty_commutator_mulEquiv_alternating eH
  have hcore : perfectCore H = ⁅H, H⁆ :=
    le_antisymm (CFSG.Quasithin.perfectCore_le_derivedSeriesOf _ 1) hle
  rw [hcore, Nat.card_congr ψ.toEquiv]
  have h2 := two_mul_nat_card_alternatingGroup (α := Fin 6)
  rw [Nat.card_perm, Nat.card_fin] at h2
  have h720 : (6 : ℕ).factorial = 720 := by decide
  omega


theorem card_stdOverlap_stdX (hK : Nat.card K = 2) : Nat.card (stdOverlap K (stdX K)) = 360 := by
  set ι := c3LeviHom K with hι
  have hinj : Function.Injective ι := c3LeviHom_injective
  have hD : C3Levi K = (⊤ : Subgroup (StatedSp 3 K)).map ι := by
    rw [← MonoidHom.range_eq_map, range_c3LeviHom]
  have hO : stdOverlap K (stdX K) = (perfectCore (complSp K (0 : Fin 3))).map ι := by
    rw [stdOverlap, stdX, hD, map_inf_centralizer_map hinj, top_inf_eq,
      ← CFSG.Quasithin.map_perfectCore, perfectCore_centralizer_nsTorusSp_eq_complSp hK]
  rw [hO, Nat.card_congr ((perfectCore (complSp K (0 : Fin 3))).equivMapOfInjective ι
    hinj).toEquiv.symm]
  exact card_perfectCore_complSp_zero_two hK

end Model

section Swap


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem card_centralizerPerfectCore_std_swap [Finite K] [CharP K 2] {t : G}
    (hw : F4Work L K t 1) (e : L ≃* adjointGroup .F4 K) {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = 3) (hS : TwoKindAt e t X₀ .swap) :
    Nat.card (centralizerPerfectCore (subgroupToG e (X₀ ⊔ stdX K))) =
      twoDiagPieceOrder .swap := by
  have hK2 : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  obtain ⟨P, hinj, hrange⟩ := exists_swapParam_nonsplit_F4_two hw e hXJ hcyc hX₀ hS
  have hYD : subgroupToG e (stdX K) ≤ subgroupToG e (C3Levi K) :=
    Subgroup.map_mono (Subgroup.map_mono (twoStdPairFacts_std K hK2).xPP_le)
  rw [subgroupToG_sup, P.centralizerPerfectCore_sup_eq hinj hrange hYD]
  have hO : perfectCore (subgroupToG e (C3Levi K) ⊓
      centralizer (subgroupToG e (stdX K) : Set G)) =
      subgroupToG e (stdOverlap K (stdX K)) := by
    rw [subgroupToG_inf_centralizer, perfectCore_subgroupToG]
    rfl
  have hOD : perfectCore (subgroupToG e (C3Levi K) ⊓
      centralizer (subgroupToG e (stdX K) : Set G)) ≤ subgroupToG e (C3Levi K) :=
    (perfectCore_le _).trans inf_le_left
  have hcardO : Nat.card (perfectCore (subgroupToG e (C3Levi K) ⊓
      centralizer (subgroupToG e (stdX K) : Set G))) = 360 := by
    rw [hO, ← Nat.card_congr (subgroupToGEquiv e (stdOverlap K (stdX K))).toEquiv]
    exact card_stdOverlap_stdX hK2
  rw [Nat.card_congr (Subgroup.equivMapOfInjective _ P.Ψ hinj).toEquiv.symm,
    Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOD).toEquiv, hcardO]
  rfl

end Swap

end CFSG.SeitzReduction.F4Pilot
