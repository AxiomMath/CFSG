module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotFiveGlobal
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMainFinal
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMainSwap
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.SeitzReduction.SeitzQ2 (SwapPairExclusion)

section HR7

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem not_normal_neighbour_pairTorus_five (hres : OmegaPlusResidualMatrixInput)
    (hset : SeitzSetting G L) {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus 5 K)) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) (k : Fin 5) :
    ¬ (((modelToG e (pairPerp (K := K) k)).subgroupOf
        (centralizer (modelToG e (pairTorus (K := K) k) : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (modelToG e (pairTorus (K := K) k) :
          Set G))))).Normal := by
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  rcases Nat.even_or_odd f with hfe | hfo
  · obtain ⟨hFR, hRC⟩ := hres 5 f K hKc le_rfl hfe
    exact not_normal_neighbour_pairTorus_of_twoSided hset hKc hq le_rfl e htC ht
      (exists_conj_eq_mul_longRoot_twoSided_plus_of_rigid hset le_rfl hKc hq e ht hKt hFR hRC) k
      rfl rfl
  · exact not_normal_neighbour_pairTorus_of_odd hset hfo hKc hq le_rfl e htC ht k rfl rfl

end HR7

section Main


variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_omegaPlus_five_of_inputs (hcat : OmegaCatalogueClausesAt 4)
    (hres : OmegaPlusResidualMatrixInput) (hlin : OmegaPlusLinearInvolutionInput 5)
    (hset : SeitzSetting G L) {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    (hP : SwapPairExclusion (matrixProjectiveDerived (coordinateQuadPlus 5 K)))
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus 5 K)) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    False := by
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hcat' : OmegaCatalogueClausesAt (5 - 1) := hcat
  have hnn := not_normal_neighbour_pairTorus_five hres hset hKc hq e ht hKt
  have h8 : ∀ k : Fin (4 + 1), OmegaHR8FieldAt t 4 f .POmegaPlus
      (modelToG e (pairTorus (K := K) k)) (modelToG e (pairPerp (K := K) k)) := fun k =>
    omegaHR8FieldAt_pairTorus_of_not_normal hset hcat' hKc hq (by omega) k e htC ht rfl rfl
      (hnn k)
  have hN : ∀ k : Fin 5, ∀ htX : t ∈ centralizer (modelToG e (pairTorus (K := K) k) : Set G),
      NeighbourOvergroupOmega (QuotientGroup.mk'
          (oddCore (centralizer (modelToG e (pairTorus (K := K) k) : Set G))) ⟨t, htX⟩)
        (((modelToG e (pairPerp (K := K) k)).subgroupOf
            (centralizer (modelToG e (pairTorus (K := K) k) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e (pairTorus (K := K) k) :
            Set G))))) (5 - 1) f := fun k htX =>
    (neighbour_overgroup_pairTorus_of_not_normal hset hcat' hKc hq (by omega) k e htC ht rfl htX
      rfl (hnn k)).1
  obtain ⟨htX0, -⟩ := h8 ⟨0, by omega⟩
  obtain ⟨r, hr, -⟩ := existsUnique_row_pairTorus hset hKc hq (by omega) e htC ht ⟨0, by omega⟩
    ⟨htX0, hN ⟨0, by omega⟩ htX0⟩
  cases r with
  | swap =>
    exact false_of_swapRow_omega_plus_of_swapPairExclusion hset hKc hq (by omega) e ht hKt hN hr hP
  | field =>
    obtain ⟨F, _, _, ι, σ, hσ, hfix⟩ := SymplecticPilot.exists_quadraticExtension K
    have : CharP F 2 := charP_of_injective_ringHom ι.injective 2
    obtain ⟨-, -, -, -, hLG, -, -, htN, ψ, hψ⟩ :=
      fieldRow_global_of_HR8_five hset hKc hq e htC ht h8 hr ι hσ hfix
        (G₀ := ⨆ j, plusNode e j) rfl
    have huniq := unique_of_omegaPlusFieldRow_of_linear hlin hset (by omega) hKc hq e ht hKt ι hσ
      hfix rfl ψ
    exact false_of_fieldRow_omegaPlus_of_unique' hset (by omega) ht hKt hLG htN hσ ψ hψ huniq

theorem omegaPlusFiveInput_of_inputs (hcat : OmegaCatalogueClausesAt 4)
    (hres : OmegaPlusResidualMatrixInput)
    (hP : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
      SwapPairExclusion (matrixProjectiveDerived (coordinateQuadPlus 5 K)))
    (hlin : OmegaPlusLinearInvolutionInput 5) : OmegaPlusFiveInput := by
  intro G _ _ L hset f K _ _ _ hK hf e t ht hKt
  have hq : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hK).2 hf
  exact false_of_omegaPlus_five_of_inputs hcat hres hlin hset hK hq (hP K hq) e ht hKt

theorem seitzExclusion_highPOmegaPlus_of_open_five (h4 : OmegaPlusFourInput)
    (h2 : OmegaPlusTwoInput) (hcat : ∀ m : ℕ, 4 ≤ m → OmegaCatalogueClausesAt m)
    (hres : OmegaPlusResidualMatrixInput)
    (hP : ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K → 5 ≤ n →
      SwapPairExclusion (matrixProjectiveDerived (coordinateQuadPlus n K)))
    (hlin : ∀ n : ℕ, 5 ≤ n → OmegaPlusLinearInvolutionInput n) :
    SeitzExclusion HighPOmegaPlus :=
  seitzExclusion_highPOmegaPlus_of_open h4
    (omegaPlusFiveInput_of_inputs (hcat 4 le_rfl) hres (fun K _ _ _ hq => hP 5 K hq le_rfl)
      (hlin 5 le_rfl)) h2
    (fun m hm => hcat m (by omega)) (omegaPlusResidualInput_of_matrixInput hres)
    (omegaPlusSwapRowInput_of_swapPairExclusion (fun n K _ _ _ hq hn => hP n K hq (by omega)))
    (fun n hn => hlin n (by omega))

end Main

end CFSG.SeitzReduction.OmegaPilot
