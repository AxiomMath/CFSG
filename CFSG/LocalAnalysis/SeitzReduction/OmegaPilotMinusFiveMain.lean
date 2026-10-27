module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusFiveUnique
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusTenHR7iii
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapGenFinal
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusFiveGlobal
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSetup
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotParamMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (fieldAutT)
open CFSG.SeitzReduction.TwistedE6Pilot (coordinateQuadMinus_fieldMap_of_fixed)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section End

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem false_of_minusFieldRow_end_of_five_le {n : ℕ} (hn : 5 ≤ n) {t : G} (ht : orderOf t = 2)
    {G₀ : Subgroup G} (htN : t ∈ normalizer (G₀ : Set G)) {F : Type} [Field F] [Finite F]
    [CharP F 2] {σ : F ≃+* F} (hσ : orderOf σ = 2) {β γ : F} (hβ : σ β = β) (hγ : σ γ = γ)
    (hirr : ∀ s : F, σ s = s → s ^ 2 + β * s + γ ≠ 0)
    (ψ : G₀ ≃* matrixProjectiveDerived (coordinateQuadMinus n F (by omega) β γ))
    (hψ : MulAut.congr ψ (G₀.normalizerMonoidHom ⟨t, htN⟩) =
      fieldAutT (coordinateQuadMinus n F (by omega) β γ) σ
        (coordinateQuadMinus_fieldMap_of_fixed (by omega) hβ hγ))
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G)) :
    False := by
  obtain ⟨E, hE2, hEInn, hEσ⟩ := omegaMinusGraphCoordinateInput_holds F n hn β γ σ hσ hβ hγ hirr
  have : E.Normal := Subgroup.normal_of_index_eq_two hE2
  have : E.FiniteIndex := ⟨by rw [hE2]; norm_num⟩
  have hρt : F4Pilot.normalizerMulAut ψ ⟨t, htN⟩ =
      fieldAutT (coordinateQuadMinus n F (by omega) β γ) σ
        (coordinateQuadMinus_fieldMap_of_fixed (by omega) hβ hγ) := hψ
  have hQ : ¬ 4 ∣ Nat.card (MulAut (matrixProjectiveDerived
      (coordinateQuadMinus n F _ β γ)) ⧸ E) := by
    change ¬ 4 ∣ E.index
    rw [hE2]
    decide
  refine EPilot.false_of_simple_of_mulAut_hom ψ htN ht huniq (QuotientGroup.mk' E) hQ
    (fun x => (QuotientGroup.eq_one_iff _).2 (hEInn x)) ?_
  rw [hρt]
  exact fun h => hEσ ((QuotientGroup.eq_one_iff _).1 h)

end End

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_omegaMinus_of_five_le_of_inputs {r : ℕ} (hcat : OmegaCatalogueClausesAt (r + 1))
    (hI : OmegaMinusInvolutionCentralizerInput (r + 2)) (hset : SeitzSetting G L) {f : ℕ}
    (hr : 3 ≤ r) {K : Type} [Field K] [Finite K] [CharP K 2] (hKc : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (r + 2) K (by omega) b c)) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    False := by
  have : IsSimpleGroup G := hset.1
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hcat' : OmegaCatalogueClausesAt (r + 2 - 1) := hcat
  have hnn := fun k : Fin (r + 1) =>
    not_normal_neighbour_minusPairTorus_of_five_le hset hKc hq (by omega : 5 ≤ r + 2) hirr e htC
      ht k rfl rfl
  have h8 : ∀ k : Fin (r + 1), OmegaHR8FieldAt t (r + 1) f .POmegaMinus
      (modelToG e (minusPairTorus (K := K) (n := r + 2) (by omega) b c k))
      (modelToG e (minusPairPerp (K := K) (n := r + 2) (by omega) b c k)) := fun k =>
    omegaHR8FieldAt_minusPairTorus hset hcat' hKc hq (by omega : 5 ≤ r + 2) hirr k e htC ht rfl
      rfl (hnn k)
  have hN : ∀ k : Fin (r + 1), ∀ htX : t ∈ centralizer
        (modelToG e (minusPairTorus (K := K) (n := r + 2) (by omega) b c k) : Set G),
      NeighbourOvergroupOmega (QuotientGroup.mk' (oddCore (centralizer
          (modelToG e (minusPairTorus (K := K) (n := r + 2) (by omega) b c k) : Set G)))
            ⟨t, htX⟩)
        (((modelToG e (minusPairPerp (K := K) (n := r + 2) (by omega) b c k)).subgroupOf
            (centralizer (modelToG e (minusPairTorus (K := K) (n := r + 2) (by omega) b c k) :
              Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer
            (modelToG e (minusPairTorus (K := K) (n := r + 2) (by omega) b c k) : Set G)))))
        (r + 2 - 1) f := fun k htX =>
    (neighbour_overgroup_minusPairTorus hset hcat' hKc hq (by omega : 5 ≤ r + 2) hirr k e htC ht
      rfl htX rfl (hnn k)).1
  obtain ⟨htX0, -⟩ := h8 (0 : Fin (r + 1))
  obtain ⟨row, hrow, -⟩ := existsUnique_row_minusPairTorus hset hKc hq (by omega : 5 ≤ r + 2)
    hirr e htC ht (0 : Fin (r + 1)) ⟨htX0, hN (0 : Fin (r + 1)) htX0⟩
  cases row with
  | swap =>
    exact false_of_swapRow_omega_minus_complete hset hKc hq (by omega : 5 ≤ r + 2) hirr e ht hKt
      hN hrow
  | field =>
    obtain ⟨F, _, _, ι, σ, hσ, hfix⟩ := SymplecticPilot.exists_quadraticExtension K
    have : CharP F 2 := charP_of_injective_ringHom ι.injective 2
    obtain ⟨hC, hglob⟩ := minusFieldRow_global_of_HR8_of_three_le hset hKc hq hr hirr e htC ht h8
      hrow ι hσ hfix
    obtain ⟨-, -, -, -, -, htN, ψ, hψ⟩ := hglob (fun k => (hC k).some) rfl
    have hu := unique_of_omegaMinusFieldRow_of_three_le hI hset hr hKc hq hirr e ht hKt ι hσ hfix
      (fun k => (hC k).some) rfl
      (ψ.trans (minusEqEquiv (by omega) (RingHom.rangeRestrictFieldEquiv_apply_coe ι b).symm
        (RingHom.rangeRestrictFieldEquiv_apply_coe ι c).symm))
    have hirr' : ∀ s : F, σ s = s → s ^ 2 + ι b * s + ι c ≠ 0 := by
      intro s hs h0
      obtain ⟨s', rfl⟩ := (hfix s).1 hs
      apply hirr s'
      apply ι.injective
      rw [map_zero, ← h0, map_add, map_add, map_mul, map_pow]
    exact false_of_minusFieldRow_end_of_five_le (by omega : 5 ≤ r + 2) ht htN hσ
      ((hfix _).2 ⟨b, rfl⟩) ((hfix _).2 ⟨c, rfl⟩) hirr' ψ hψ hu

theorem seitzExclusion_highPOmegaMinus_of_centralizer_of_five_le (h4 : OmegaMinusFourInput)
    (h2 : OmegaMinusTwoInput) (hcat : ∀ m : ℕ, 4 ≤ m → OmegaCatalogueClausesAt m)
    (hI : ∀ n : ℕ, 5 ≤ n → OmegaMinusInvolutionCentralizerInput n) :
    SeitzExclusion HighPOmegaMinus := by
  refine seitzExclusion_highPOmegaMinus_of_cases
    (fun G _ _ L hset n f hn K _ _ _ b c hirr hK hf e t ht hKt => ?_)
    (fun G _ _ L hset n hn K _ _ _ b c hirr hK e t ht hKt =>
      h2 G L hset n hn K b c hirr hK e t ht hKt)
  have hq : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hK).2 hf
  rcases (show n = 4 ∨ 5 ≤ n by omega) with rfl | h5
  · exact h4 G L hset f K b c hirr hK hf e t ht hKt
  · obtain ⟨r, rfl⟩ : ∃ r, n = r + 2 := ⟨n - 2, by omega⟩
    exact false_of_omegaMinus_of_five_le_of_inputs (hcat (r + 1) (by omega))
      (hI (r + 2) h5) hset (by omega) hK hq hirr e ht hKt

end Main

end CFSG.SeitzReduction.OmegaPilot
