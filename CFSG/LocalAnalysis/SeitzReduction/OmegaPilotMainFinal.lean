module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMain
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEndFieldAut
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotUniqueLinear
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotGlobalClass
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSetup
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotParamMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (fieldAutT)

section Endgame

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_fieldRow_omegaPlus_of_unique' (hset : SeitzSetting G L) {n : ℕ} (hn : 5 ≤ n)
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {G₀ : Subgroup G} (hLG : L ≤ G₀) (htN : t ∈ normalizer (G₀ : Set G))
    {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F} (hσ : orderOf σ = 2)
    (ψ : G₀ ≃* matrixProjectiveDerived (coordinateQuadPlus n F))
    (hψ : MulAut.congr ψ (G₀.normalizerMonoidHom ⟨t, htN⟩) =
      fieldAutT (coordinateQuadPlus n F) σ (E7Pilot.coordinateQuadPlus_fieldMap n σ))
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) →
      g ∈ normalizer (G₀ : Set G)) : False :=
  false_of_fieldRow_omegaPlus_of_unique omegaPlusAutNormalFormInput_holds hset hn ht hKt hLG htN
    hσ ψ hψ huniq

end Endgame


variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_omegaPlus_high_of_linear {m : ℕ} (hcat : OmegaCatalogueClausesAt m)
    (hres : OmegaPlusResidualInput) (hswap : OmegaPlusSwapRowInput)
    (hlin : OmegaPlusLinearInvolutionInput (m + 1))
    (hset : SeitzSetting G L) {f : ℕ} (hm : 5 ≤ m) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (m + 1) K)) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    False := by
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hcat' : OmegaCatalogueClausesAt (m + 1 - 1) := hcat
  have hnn := not_normal_neighbour_pairTorus_of_residualInput hres hset hKc hq (by omega) e ht hKt
  have h8 : ∀ k : Fin (m + 1), OmegaHR8FieldAt t m f .POmegaPlus
      (UnitaryPilot.modelToG e (pairTorus (K := K) k))
      (UnitaryPilot.modelToG e (pairPerp (K := K) k)) := fun k => by
    exact omegaHR8FieldAt_pairTorus_of_not_normal hset hcat' hKc hq (by omega) k e htC ht
      rfl rfl (hnn k)
  have hN : ∀ k : Fin (m + 1), ∀ htX : t ∈ centralizer
      (UnitaryPilot.modelToG e (pairTorus (K := K) k) : Set G),
      NeighbourOvergroupOmega (QuotientGroup.mk'
          (oddCore (centralizer (UnitaryPilot.modelToG e (pairTorus (K := K) k) : Set G)))
            ⟨t, htX⟩)
        (((UnitaryPilot.modelToG e (pairPerp (K := K) k)).subgroupOf
            (centralizer (UnitaryPilot.modelToG e (pairTorus (K := K) k) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer
            (UnitaryPilot.modelToG e (pairTorus (K := K) k) : Set G))))) (m + 1 - 1) f :=
    fun k htX => (neighbour_overgroup_pairTorus_of_not_normal hset hcat' hKc hq (by omega) k e htC
      ht rfl htX rfl (hnn k)).1
  obtain ⟨htX0, -⟩ := h8 ⟨0, by omega⟩
  obtain ⟨r, hr, -⟩ := existsUnique_row_pairTorus hset hKc hq (by omega) e htC ht ⟨0, by omega⟩
    ⟨htX0, hN ⟨0, by omega⟩ htX0⟩
  cases r with
  | swap => exact hswap G L hset (m + 1) f K hKc hq (by omega) e t ht hKt hN hr
  | field =>
    obtain ⟨F, _, _, ι, σ, hσ, hfix⟩ := SymplecticPilot.exists_quadraticExtension K
    have : CharP F 2 := charP_of_injective_ringHom ι.injective 2
    obtain ⟨-, -, -, -, hLG, -, -, htN, ψ, hψ⟩ :=
      fieldRow_global_of_HR8 hset hKc hq hm e htC ht h8 hr ι hσ hfix (G₀ := ⨆ j, plusNode e j)
        rfl
    have huniq := unique_of_omegaPlusFieldRow_of_linear hlin hset (by omega) hKc hq e ht hKt ι hσ
      hfix rfl ψ
    exact false_of_fieldRow_omegaPlus_of_unique' hset (by omega) ht hKt hLG htN hσ ψ hψ huniq

theorem seitzExclusion_highPOmegaPlus_of_open (h4 : OmegaPlusFourInput)
    (h5 : OmegaPlusFiveInput) (h2 : OmegaPlusTwoInput)
    (hcat : ∀ m : ℕ, 5 ≤ m → OmegaCatalogueClausesAt m) (hres : OmegaPlusResidualInput)
    (hswap : OmegaPlusSwapRowInput)
    (hlin : ∀ n : ℕ, 6 ≤ n → OmegaPlusLinearInvolutionInput n) :
    SeitzExclusion HighPOmegaPlus := by
  refine seitzExclusion_highPOmegaPlus_of_cases
    (fun G _ _ L hset n f K _ _ _ hK hf hn e t ht hKt => ?_) h2
  have hq : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hK).2 hf
  rcases (show n = 4 ∨ n = 5 ∨ 6 ≤ n by omega) with rfl | rfl | h6
  · exact h4 G L hset f K hK hf e t ht hKt
  · exact h5 G L hset f K hK hf e t ht hKt
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact false_of_omegaPlus_high_of_linear (hcat m (by omega)) hres hswap (hlin (m + 1) h6)
      hset (by omega) hK hq e ht hKt

end CFSG.SeitzReduction.OmegaPilot
