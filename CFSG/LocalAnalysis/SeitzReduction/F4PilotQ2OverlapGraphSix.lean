module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapGraphLinParam
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapGraphGL4

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.Universal.Symplectic.SpExtras
open CFSG.SeitzReduction.SymplecticPilot (q2Embed q2Block q2Embed_mem_q2Block_iff planeCoordsQ2
  q2Coord)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def twoLinEquiv6 :
    ((planeCoordsQ2 0 ({3, 0} : Finset (Fin 4)))ᶜ : Finset (Fin (2 * 4 + 0))) ≃ Fin 4 :=
  coordEquivOfList _ (q2Coord 4 0 ∘ twoLinCoords6)
    ((q2Coord 4 0).injective.comp twoLinCoords6_injective) mem_compl_planeCoordsQ2_iff6

theorem card_q2Block_three_zero_six (hK : Nat.card K = 2) :
    Nat.card (q2Block 0 K ({3, 0} : Finset (Fin 4))) = 20160 := by
  rw [SymplecticPilot.q2Block, card_blockSpecialLinear_eq _ twoLinEquiv6 (twoRingEquiv hK),
    Matrix.card_GL_field]
  simp [Fin.prod_univ_four, ZMod.card]

theorem q2Embed_elt_positiveLong_mem_six (hK : Nat.card K = 2) :
    q2Embed 0 hK (elt (.positiveLong (1 : Fin 4)) (1 : K)) ∈
      q2Block 0 K ({3, 0} : Finset (Fin 4)) :=
  (q2Embed_mem_q2Block_iff hK).2
    (CFSG.SeitzReduction.SymplecticPilot.elt_positiveLong_mem_spBlock (by decide) 1)

theorem q2Embed_elt_positiveSum_mem_six (hK : Nat.card K = 2) :
    q2Embed 0 hK (elt (.positiveSum (1 : Fin 4) 2 (by decide)) (1 : K)) ∈
      q2Block 0 K ({3, 0} : Finset (Fin 4)) :=
  (q2Embed_mem_q2Block_iff hK).2
    (CFSG.SeitzReduction.SymplecticPilot.elt_positiveSum_mem_spBlock (by decide) (by decide)
      (by decide) 1)

set_option linter.unusedSimpArgs false in
theorem card_centralizer_transvection_six (hK : Nat.card K = 2) :
    Nat.card (centralizer ({q2Embed 0 hK (elt (.positiveLong (1 : Fin 4)) (1 : K))} :
        Set (SpecialLinearGroup (Fin (2 * 4 + 0)) K)) ⊓ q2Block 0 K ({3, 0} : Finset (Fin 4)) :
      Subgroup (SpecialLinearGroup (Fin (2 * 4 + 0)) K)) = 192 := by
  rw [SymplecticPilot.q2Block, card_centralizer_inf_blockSpecialLinear_eq _ twoLinEquiv6
    (twoRingEquiv hK) (q2Embed_elt_positiveLong_mem_six hK) (g := gl4T0) ?_,
    gl4_card_centralizer_t0]
  intro a b
  rw [twoLinEquiv6, coe_coordEquivOfList_symm, coe_coordEquivOfList_symm, Function.comp_apply,
    Function.comp_apply, CFSG.SeitzReduction.SymplecticPilot.q2Embed_apply_q2Coord, mat_elt]
  fin_cases a <;> fin_cases b <;>
    simp [twoLinCoords6, E, gl4T0, gl4T0M, Matrix.one_apply, Matrix.single_apply]

set_option linter.unusedSimpArgs false in
theorem card_centralizer_rankTwo_six (hK : Nat.card K = 2) :
    Nat.card (centralizer ({q2Embed 0 hK (elt (.positiveSum (1 : Fin 4) 2 (by decide)) (1 : K))} :
        Set (SpecialLinearGroup (Fin (2 * 4 + 0)) K)) ⊓ q2Block 0 K ({3, 0} : Finset (Fin 4)) :
      Subgroup (SpecialLinearGroup (Fin (2 * 4 + 0)) K)) = 96 := by
  rw [SymplecticPilot.q2Block, card_centralizer_inf_blockSpecialLinear_eq _ twoLinEquiv6
    (twoRingEquiv hK) (q2Embed_elt_positiveSum_mem_six hK) (g := gl4U0) ?_,
    gl4_card_centralizer_u0]
  intro a b
  rw [twoLinEquiv6, coe_coordEquivOfList_symm, coe_coordEquivOfList_symm, Function.comp_apply,
    Function.comp_apply, CFSG.SeitzReduction.SymplecticPilot.q2Embed_apply_q2Coord, mat_elt]
  fin_cases a <;> fin_cases b <;>
    simp [twoLinCoords6, E, gl4U0, gl4U0M, Matrix.one_apply, Matrix.single_apply]

theorem twoGraphModelValues_linear6 (hK : Nat.card K = 2) :
    TwoGraphModelValues .linear6 K (q2Block 0 K ({3} : Finset (Fin 4))) (twoLinIota 0 hK) := by
  have hO := map_centralizerPerfectCore_twoLinIota (K := K) 0 hK
  have hinj := (q2Block 0 K ({3} : Finset (Fin 4))).subtype_injective
  refine ⟨?_, fun _ => ⟨?_, ?_⟩⟩
  · rw [← Subgroup.card_map_of_injective hinj, hO, card_q2Block_three_zero_six hK]
    rfl
  · rw [← Subgroup.card_map_of_injective hinj, ← centralizer_map_inf_map_of_injective hinj, hO,
      Subgroup.map_map, centralizer_map_rootGroup_eq hK _ stdVec_positiveLong_one,
      MonoidHom.comp_apply, coe_subtype, coe_twoLinIota_elt_positiveLong,
      card_centralizer_transvection_six hK]
    rfl
  · rw [← Subgroup.card_map_of_injective hinj, ← centralizer_map_inf_map_of_injective hinj, hO,
      Subgroup.map_map, centralizer_map_rootGroup_eq hK _ stdVec_positiveSum_one_two,
      MonoidHom.comp_apply, coe_subtype, coe_twoLinIota_elt_positiveSum,
      card_centralizer_rankTwo_six hK]
    rfl

theorem twoOverlapInvAt_linear6 : TwoOverlapInvAt .linear6 :=
  twoOverlapInvAt_linear6_of_values fun _ _ _ _ hK => twoGraphModelValues_linear6 hK

@[expose] def TwoOverlapInvUnitaryOmegaInput : Prop :=
  TwoOverlapInvAt .unitary6 ∧ TwoOverlapInvAt .unitary7 ∧ TwoOverlapInvAt .omegaPlus8 ∧
    TwoOverlapInvAt .omegaMinus8

theorem twoOverlapInvGraphInput_of_unitaryOmega (h : TwoOverlapInvUnitaryOmegaInput) :
    TwoOverlapInvGraphInput := by
  intro κ hκ
  cases κ with
  | field => exact absurd rfl hκ.1
  | swap => exact absurd rfl hκ.2
  | linear6 => exact twoOverlapInvAt_linear6
  | linear7 => exact twoOverlapInvAt_linear7
  | unitary6 => exact h.1
  | unitary7 => exact h.2.1
  | omegaPlus8 => exact h.2.2.1
  | omegaMinus8 => exact h.2.2.2

end CFSG.SeitzReduction.F4Pilot
