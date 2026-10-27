module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotFourOrth
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindOmegaMinusPieces
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainPieceTables
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotParamMain

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.SeitzReduction.UnitaryPilot (modelToG OddCentralSplit)
open CFSG.SeitzReduction.F4Pilot (ordSL natCard_SL_two ordSL_two_lt_sq ordSL_two_lt_ordSL_two_sq)

@[expose] def SpOmegaSiegelCentralInput (κ : Sp2mKind) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ n → Even n →
    Nat.card K = 2 ^ f → 2 ≤ f → ∀ (e : L ≃* StatedSp n K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin n, RootKindSp e t f k κ) → SpOmegaRowGlobal e t f κ →
        ∀ h ∈ centralizer (modelToG e (siegelTorus K n) : Set G),
          orderOf (t * h * t⁻¹ * h⁻¹) ≠ 2

section Kinds

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {n : ℕ}

theorem siegel_commutator_ne_two_of_pieceOrder (hcat : LinearPilot.SLmCatalogueClausesAt n)
    (hdet : LinearPilot.SLmEvenTypeDetAt n) (hsplit : OddCentralSplit (siegelLevi K n))
    (hset : SeitzSetting G L) {f : ℕ} (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hn : 3 ≤ n)
    (e : L ≃* StatedSp n K) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hM : Nat.card (pieceCore e ({⟨0, by omega⟩} : Finset (Fin n))) = ordSL 2 (Nat.card K)) :
    ∀ h ∈ centralizer (modelToG e (siegelTorus K n) : Set G), orderOf (t * h * t⁻¹ * h⁻¹) ≠ 2 := by
  have : Finite K := LinearPilot.finite_of_card_eq_two_pow hKc
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow hKc
  have hq : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  obtain ⟨F, _, _, ι, σ, hσ, hfix⟩ := exists_quadraticExtension K
  obtain ⟨hσ1, hσσ⟩ := ne_one_and_mul_self_of_orderOf_eq_two hσ
  have hF : Nat.card F = Nat.card K ^ 2 := by
    rw [LinearPilot.natCard_eq_two_pow_of_fixedField hKc ι hσ1 hσσ hfix, hKc, ← pow_mul,
      mul_comm]
  have h0 : (⟨0, by omega⟩ : Fin n).val + 1 < n := by simp; omega
  rcases siegel_normal_or_fieldParam_or_swapParam hcat hdet hset hKc hf hn e htC ht hsplit ι hσ1
    hσσ hfix with ⟨htX, hnorm⟩ | hP | hS
  · have hcen := mk_mem_center_of_siegel_normal hset hKc hf hn e htC ht htX hnorm
    intro h hh hord
    exact false_of_mk_mem_center_of_orderOf_commutator htX hh hord hcen
  · obtain ⟨P⟩ := hP
    have h1 := P.natCard_pieceCore_singleton hq hn h0
    rw [hM, hF] at h1
    have := ordSL_two_lt_ordSL_two_sq (q := Nat.card K) (by omega)
    omega
  · obtain ⟨S⟩ := hS
    have h1 := S.natCard_pieceCore_singleton hq hn h0
    rw [hM] at h1
    have := ordSL_two_lt_sq (q := Nat.card K) (by omega)
    omega

end Kinds

theorem bSiegel_natCard_modelToG {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]
    {n : ℕ} (e : L ≃* StatedSp n K) (A : Subgroup (StatedSp n K)) :
    Nat.card (modelToG e A) = Nat.card A := by
  rw [UnitaryPilot.modelToG_def, Subgroup.card_map_of_injective L.subtype_injective,
    Subgroup.card_map_of_injective e.symm.injective]

section Rows


theorem spOmegaSiegelCentralInput_omegaPlus_of_clauses
    (hcat : ∀ m, 4 ≤ m → LinearPilot.SLmCatalogueClausesAt m)
    (hdet : ∀ m, 4 ≤ m → LinearPilot.SLmEvenTypeDetAt m) :
    SpOmegaSiegelCentralInput .omegaPlus := by
  intro G _ _ L hset n f K _ _ _ hn _ hKc hf e t ht hKt hroot _
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hpar := kOmegaParams_of_rootKind hset (by omega : 2 ≤ m) hKc hf e htC ht hroot
  have hM := kOmega_pieceCore_short_eq_modelToG (by omega : 2 ≤ m) hKc hf e hpar ⟨0, by omega⟩
    (by simp)
  refine siegel_commutator_ne_two_of_pieceOrder (hcat _ hn) (hdet _ hn)
    (oddCentralSplit_siegelLevi (by omega)) hset hKc hf (by omega) e htC ht ?_
  rw [hM, bSiegel_natCard_modelToG, kOmega_card_simpleRootSL2, natCard_SL_two]

theorem spOmegaSiegelCentralInput_omegaMinus_of_clauses
    (hcat : ∀ m, 4 ≤ m → LinearPilot.SLmCatalogueClausesAt m)
    (hdet : ∀ m, 4 ≤ m → LinearPilot.SLmEvenTypeDetAt m) :
    SpOmegaSiegelCentralInput .omegaMinus := by
  intro G _ _ L hset n f K _ _ _ hn _ hKc hf e t ht hKt hroot _
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hpar := kOmMParams_of_rootKind hset (by omega : 2 ≤ m) hKc hf e htC ht hroot
  have hM := kOmM_pieceCore_short_eq_modelToG (by omega : 2 ≤ m) hKc hf e hpar ⟨0, by omega⟩
    (by simp)
  refine siegel_commutator_ne_two_of_pieceOrder (hcat _ hn) (hdet _ hn)
    (oddCentralSplit_siegelLevi (by omega)) hset hKc hf (by omega) e htC ht ?_
  rw [hM, bSiegel_natCard_modelToG, kOmega_card_simpleRootSL2, natCard_SL_two]

end Rows

end CFSG.SeitzReduction.SymplecticPilot
