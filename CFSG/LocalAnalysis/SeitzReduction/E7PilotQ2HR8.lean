module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2Position
import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR8Instances
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotHR8

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley
open CFSG.SeitzReduction.OmegaPilot (NeighbourOvergroupOmega OmegaNeighbourAlternative
  OmegaCatalogueClausesAt)
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput)

variable {K : Type} [Field K] {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem neighbour_overgroup_E7_nonsplit_two (hcat : OmegaCatalogueClausesAt 6)
    (hset : StandardSetting G L) (hK : Nat.card K = 2) (e : L ≃* adjointGroup .E7 K) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {A : Subgroup (adjointGroup .E7 K)} (hAJ : A ≤ posJE7 K) (hA : Nat.card A = 3)
    {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((EPilot.perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype) :
    NeighbourOvergroupOmega (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) 6 1 ∧
      ∀ Lc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsComponent Lc →
        ⁅(D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))), Lc⁆ ≠ ⊥ →
        OmegaNeighbourAlternative
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
          ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) Lc 6 1 := by
  have hK' : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  have := F4Pilot.finite_of_natCard_eq_two_pow hK'
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK'
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  obtain ⟨hcomp, hsyl, hstd⟩ :=
    neighbour_standard_E7_nonsplit_two hset.standard htK.1 ht hKt hK e hAJ hA hX htX hDe
  have hXJ : X ≤ ((posJE7 K).map e.symm.toMonoidHom).map L.subtype := by
    rw [hX]
    exact map_mono (map_mono hAJ)
  have hXodd : Odd (Nat.card X) := by
    rw [hX, natCard_map_map_E7, hA]
    decide
  have hnn := not_normal_map_oddCore_neighbour_E7_two hset hK e ht hKt hXodd hXJ hDe hsyl
  have hDX : D ≤ centralizer (X : Set G) := hDe ▸ map_perpLevi_le_centralizer_E7_of_charTwo e hXJ
  have hAne : A ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hA
    omega
  have hXG : centralizer (X : Set G) ≠ ⊤ :=
    F4Pilot.centralizer_ne_top_of_ne_bot hset.simple hset.nonab
      (hX ▸ F4Pilot.map_map_symm_ne_bot e hAne)
  have hDq : CFSG.IsQuasisimple D := hDe ▸ isQuasisimple_map_perpLevi_E7 e
  have hDm := lieModel_quotient_center_map_map_perpLevi_E7 hK' e (G := G) (L := L)
  have hZD := odd_card_center_map_map_perpLevi_E7 e (G := G) (L := L)
  rw [← hDe] at hDm hZD
  exact OmegaPilot.neighbour_overgroup_omega (six_ne_four_pair 1) hcat hset.kProper hXG htX ht
    hDX hDq (Or.inl rfl) hDm hZD hcomp hsyl hstd hnn

end CFSG.SeitzReduction.E7Pilot
