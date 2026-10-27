module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotFourTrivial
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotSiegelParamSwap
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotSiegelConsistency
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotMainInputs
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapLiftSplit
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatTypeDet

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)
open CFSG.SeitzReduction.UnitaryPilot (OddCentralSplit)

theorem oddCentralSplit_siegelLevi
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 1 ≤ n) : OddCentralSplit (siegelLevi K n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact (LinearPilot.oddCentralSplit_specialLinearGroup (m := m) (F := K)).of_mulEquiv
    siegelLeviEquiv

section Field

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {F : Type}
  [Field F] [Finite F] {n : ℕ}

theorem nonempty_siegelFieldParam_of_fieldNeighbourParam
    (hcat : LinearPilot.SLmCatalogueClausesAt n) (hdet : LinearPilot.SLmEvenTypeDetAt n)
    (hsplit : OddCentralSplit (siegelLevi K n)) (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hn : 3 ≤ n) (e : L ≃* StatedSp n K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (ι : K →+* F) {σ : F ≃+* F}
    (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    (P : FieldNeighbourParam e t ι σ ⟨2, by omega⟩) : Nonempty (SiegelFieldParam e t ι σ) := by
  have : Finite K := LinearPilot.finite_of_card_eq_two_pow hKc
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow hKc
  have : CharP F 2 := charP_of_injective_ringHom ι.injective 2
  have hq : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  have hF : Nat.card F = Nat.card K ^ 2 := by
    rw [LinearPilot.natCard_eq_two_pow_of_fixedField hKc ι hσ1 hσσ hfix, hKc, ← pow_mul,
      mul_comm]
  rcases siegel_normal_or_fieldParam_or_swapParam hcat hdet hset hKc hf hn e htC ht hsplit ι hσ1
    hσσ hfix with ⟨htX, hnorm⟩ | hP | hS
  · exact (false_of_fieldNeighbourParam_of_siegel_normal hset hKc hf hn e htC ht hσ1 P
      (j := ⟨0, by omega⟩) (by simp; omega) (by simp [Fin.ext_iff]) (by simp) htX hnorm).elim
  · exact hP
  · exact hS.elim fun S => (false_of_fieldNeighbourParam_of_siegelSwapParam hq hn hF P S).elim

theorem commute_pieceCore_zero_two_of_fieldNeighbourParam
    (hcat : LinearPilot.SLmCatalogueClausesAt n) (hdet : LinearPilot.SLmEvenTypeDetAt n)
    (hsplit : OddCentralSplit (siegelLevi K n)) (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hn : 4 ≤ n) (e : L ≃* StatedSp n K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (ι : K →+* F) {σ : F ≃+* F}
    (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    (P : FieldNeighbourParam e t ι σ ⟨2, by omega⟩) :
    ∀ a ∈ pieceCore e ({(⟨0, by omega⟩ : Fin n)} : Finset (Fin n)),
      ∀ b ∈ pieceCore e ({(⟨2, by omega⟩ : Fin n)} : Finset (Fin n)), Commute a b := by
  have hq : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  obtain ⟨S⟩ := nonempty_siegelFieldParam_of_fieldNeighbourParam hcat hdet hsplit hset hKc hf
    (by omega) e htC ht ι hσ1 hσσ hfix P
  intro a ha b hb
  exact (mem_centralizer_iff.1 (S.pieceCore_zero_le_centralizer_pieceCore_two hq hn ha) b hb).symm

end Field

theorem ne_one_and_mul_self_of_orderOf_eq_two {F : Type} [Field F] {σ : F ≃+* F}
    (hσ : orderOf σ = 2) : σ ≠ 1 ∧ σ * σ = 1 := by
  refine ⟨fun h => ?_, by rw [← sq, ← hσ, pow_orderOf_eq_one]⟩
  rw [h, orderOf_one] at hσ
  exact absurd hσ (by norm_num)

section Four

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {F : Type}
  [Field F] [Finite F]

theorem commute_pieceCore_zero_two_four (hcat : LinearPilot.SLmCatalogueClausesAt 4)
    (hdet : LinearPilot.SLmEvenTypeDetAt 4) (hsplit : OddCentralSplit (siegelLevi K 4))
    (hset : SeitzSetting G L) {f : ℕ} (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp 4 K) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (ι : K →+* F) {σ : F ≃+* F} (hσ : orderOf σ = 2) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    (hparam : ∀ k : Fin 4, Nonempty (FieldNeighbourParam e t ι σ k)) :
    ∀ a ∈ pieceCore e ({0} : Finset (Fin 4)), ∀ b ∈ pieceCore e ({2} : Finset (Fin 4)),
      Commute a b :=
  commute_pieceCore_zero_two_of_fieldNeighbourParam hcat hdet hsplit hset hKc hf le_rfl e htC ht
    ι (ne_one_and_mul_self_of_orderOf_eq_two hσ).1 (ne_one_and_mul_self_of_orderOf_eq_two hσ).2
    hfix (hparam 2).some

end Four

theorem spFourOrthInput_of_clauses
    (hcat : LinearPilot.SLmCatalogueClausesAt 4)
    (hdet : LinearPilot.SLmEvenTypeDetAt 4) : SpFourOrthInput := by
  intro G _ _ L hset f K _ _ _ hKc hf e t ht hCt F _ _ ι σ hσ hfix hparam
  exact commute_pieceCore_zero_two_four hcat hdet (oddCentralSplit_siegelLevi (by norm_num)) hset
    hKc hf e (LinearPilot.mem_centralizer_of_inf_eq_zpowers hCt) ht ι hσ hfix hparam

theorem spFourOrthInput_of_catalogue
    (hcat : LinearPilot.SLmCatalogueClausesAt 4) : SpFourOrthInput :=
  spFourOrthInput_of_clauses hcat (LinearPilot.slmEvenTypeDetAt (by norm_num))

end CFSG.SeitzReduction.SymplecticPilot
