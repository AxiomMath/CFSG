module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapOmSixPlusChain
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapOmMinus
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapOmSixMinus

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Matrix Subgroup CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem omQ6p_index : ((StatedOmega omQ6p).subgroupOf (omIsoGroup omQ6p)).index = 2 :=
  omIndex_quadPlus_three

@[expose] def omMiRZ : GL omPI6 (ZMod 2) := ⟨omNR, omNR, omNR_sq, omNR_sq⟩

theorem omMiRZ_mem_iso : omMiRZ ∈ omIsoGroup omQ6p := by
  change ∀ v, omQ6p (omNR *ᵥ v) = omQ6p v
  decide +kernel

theorem omMiRZ_comm_HS : omMiRZ ∈ centralizer ({omMiHSZ} : Set (GL omPI6 (ZMod 2))) :=
  mem_centralizer_singleton_iff.2 (Units.ext (by decide +kernel))

theorem omMiRZ_comm_HL : omMiRZ ∈ centralizer ({omMiHLZ} : Set (GL omPI6 (ZMod 2))) :=
  mem_centralizer_singleton_iff.2 (Units.ext (by decide +kernel))

theorem omMiRZ_not_mem : omMiRZ ∉ StatedOmega omQ6p :=
  omNotMem_quadPlus_three omMiRZ (Pi.single (Sum.inl 2) 1 + Pi.single (Sum.inr 2) 1)
    (by decide +kernel) (by decide +kernel)

theorem omMi_card_centralizer {h : GL omPI6 (ZMod 2)} (hΩ : h ∈ StatedOmega omQ6p)
    (hr : omMiRZ ∈ centralizer ({h} : Set (GL omPI6 (ZMod 2)))) {n : ℕ}
    (hC : Nat.card (omIsoGroup omQ6p ⊓ centralizer ({h} : Set (GL omPI6 (ZMod 2))) :
      Subgroup (GL omPI6 (ZMod 2))) = 2 * n) :
    Nat.card (centralizer ({(⟨h, hΩ⟩ : StatedOmega omQ6p)} : Set (StatedOmega omQ6p))) = n := by
  have e1 := card_centralizer_singleton_inf_range (StatedOmega omQ6p).subtype_injective
    (⟨h, hΩ⟩ : StatedOmega omQ6p)
  rw [Subgroup.range_subtype] at e1
  rw [← e1]
  have h2 := card_inf_mul_two (G₀ := omIsoGroup omQ6p) (N := StatedOmega omQ6p)
    (H := omIsoGroup omQ6p ⊓ centralizer ({h} : Set (GL omPI6 (ZMod 2)))) inf_le_left
    omQ6p_index ⟨omMiRZ_mem_iso, hr⟩ omMiRZ_not_mem
  have e2 : omIsoGroup omQ6p ⊓ centralizer ({h} : Set (GL omPI6 (ZMod 2))) ⊓
      StatedOmega omQ6p = centralizer ({h} : Set (GL omPI6 (ZMod 2))) ⊓ StatedOmega omQ6p := by
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨-, hx⟩, hx'⟩
      exact ⟨hx, hx'⟩
    · rintro ⟨hx, hx'⟩
      exact ⟨⟨statedOmega_le_omIsoGroup _ hx', hx⟩, hx'⟩
  rw [e2, hC] at h2
  change Nat.card (centralizer ({h} : Set (GL omPI6 (ZMod 2))) ⊓ StatedOmega omQ6p :
    Subgroup (GL omPI6 (ZMod 2))) = n
  omega

theorem omMiHSZ_mem : omMiHSZ ∈ StatedOmega omQ6p := by
  have e : omMiHSZ = ⁅(⟨omNE1, omNE1, omNE1_sq, omNE1_sq⟩ : GL omPI6 (ZMod 2)),
      ⟨omNE2, omNE2, omNE2_sq, omNE2_sq⟩⁆ := Units.ext omNHS_eq.symm
  rw [e]
  exact commutator_mem_statedOmega omNE1_isom omNE2_isom

theorem omMiHLZ_mem : omMiHLZ ∈ StatedOmega omQ6p := by
  have e : omMiHLZ = ⁅(⟨omNE3, omNE3, omNE3_sq, omNE3_sq⟩ : GL omPI6 (ZMod 2)),
      ⟨omNE4, omNE4, omNE4_sq, omNE4_sq⟩⁆ := Units.ext omNHL_eq.symm
  rw [e]
  exact commutator_mem_statedOmega omNE3_isom omNE4_isom

theorem omSixPlusCentValues_holds : OmSixPlusCentValues := by
  intro K _ _ _ hK
  refine ⟨?_, ?_⟩
  · rw [card_centralizer_omTransfer hK (statedQuadPlus_omCast 3)
      (x := ⟨omMiHLZ, omMiHLZ_mem⟩) rfl]
    exact omMi_card_centralizer omMiHLZ_mem omMiRZ_comm_HL (by rw [omMi_card_CL])
  · rw [card_centralizer_omTransfer hK (statedQuadPlus_omCast 3)
      (x := ⟨omMiHSZ, omMiHSZ_mem⟩) rfl]
    exact omMi_card_centralizer omMiHSZ_mem omMiRZ_comm_HS (by rw [omMi_card_CS])

theorem twoOmegaMinusModelValues_holds : TwoOmegaMinusModelValues :=
  twoOmegaMinusModelValues_of_six omSixPlusCentValues_holds

end CFSG.SeitzReduction.F4Pilot
