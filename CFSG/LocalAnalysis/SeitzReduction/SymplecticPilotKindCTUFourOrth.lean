module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUFourBar
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotFourOrth
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUAlignFourRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotParamMain

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply unitaryInvolution_involutive)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical (matrixIsometryGroup)
open CFSG.SeitzReduction.UnitaryPilot (modelToG OddCentralSplit)

section Comm

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem commute_pieceCore_zero_two_of_ctuParam (hcat : LinearPilot.SLmCatalogueClausesAt 4)
    (hdet : LinearPilot.SLmEvenTypeDetAt 4) (hsplit : OddCentralSplit (siegelLevi K 4))
    (hset : SeitzSetting G L) {f : ℕ} (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp 4 K) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = (2 ^ f) ^ 2) {ε : ℕ}
    {hε : ε ≤ 1} {ι : K →+* F} {hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c} {k : Fin 4}
    (P : CtuParam ε hε (unitaryInvolution F 2 f) ι hι e k)
    (hP : ∀ x, t * P.Φ x * t⁻¹ = P.Φ ⟨ctuaBarAut _ (unitaryInvolution_involutive hF) _ x,
      ctuf_bar_mem_ctuBlock _ x.2⟩) :
    ∀ a ∈ pieceCore e ({0} : Finset (Fin 4)), ∀ b ∈ pieceCore e ({2} : Finset (Fin 4)),
      Commute a b := by
  have hq : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  obtain ⟨F', _, _, ι', σ, hσ, hfix⟩ := exists_quadraticExtension K
  obtain ⟨hσ1, hσσ⟩ := ne_one_and_mul_self_of_orderOf_eq_two hσ
  rcases siegel_normal_or_fieldParam_or_swapParam hcat hdet hset hKc hf (by norm_num) e htC ht
    hsplit ι' hσ1 hσσ hfix with ⟨htX, hnorm⟩ | hS | hS
  · exact (false_of_siegel_normal_of_ctuParam hset hKc hF hf le_rfl htC ht P hP htX hnorm).elim
  · obtain ⟨S⟩ := hS
    intro a ha b hb
    exact (mem_centralizer_iff.1 (S.pieceCore_zero_le_centralizer_pieceCore_two hq le_rfl ha) b
      hb).symm
  · obtain ⟨S⟩ := hS
    intro a ha b hb
    exact (mem_centralizer_iff.1 (S.pieceCore_zero_le_centralizer_pieceCore_two hq le_rfl ha) b
      hb).symm

end Comm

theorem spUnitaryEvenFourOrthInput_of_clauses
    (hcat : LinearPilot.SLmCatalogueClausesAt 4) (hdet : LinearPilot.SLmEvenTypeDetAt 4) :
    SpUnitaryEvenFourOrthInput := by
  intro G _ _ L hset f K _ _ _ hKc hf e t ht hKt hP
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  obtain ⟨K', _, h, _, C₀, hC, hC₀, ι', ⟨U⟩⟩ := hP 3
  have : Finite K' := h.finite
  have : CharP K' 2 := h.charP
  have hF : Nat.card K' = (2 ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  set ι : K →+* K' := h.fixedField.subtype.comp (ι' : K →+* h.fixedField) with hιdef
  have hι : ∀ c, unitaryInvolution K' 2 f (ι c) = ι c := fun c => by
    rw [unitaryInvolution_apply, ← h.bar_apply]
    exact h.mem_fixedField.1 (ι' c).2
  exact commute_pieceCore_zero_two_of_ctuParam hcat hdet (oddCentralSplit_siegelLevi (by norm_num))
    hset hKc hf e htC ht hF (ctuParamOfUnitary (hι := hι) (RingEquiv.refl K') (fun _ => rfl) U)
    (ctuParamOfUnitary_conj (hι := hι) (unitaryInvolution_involutive hF) _ _ U)

theorem spUnitaryOddFourOrthInput_of_clauses
    (hcat : LinearPilot.SLmCatalogueClausesAt 4) (hdet : LinearPilot.SLmEvenTypeDetAt 4) :
    SpUnitaryOddFourOrthInput := by
  intro G _ _ L hset f K _ _ _ hKc hf e t ht hKt hP
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  obtain ⟨K', _, h, _, C₀, hC, hC₀, hβ⟩ := hP 3
  have : Finite K' := h.finite
  have : CharP K' 2 := h.charP
  have : Finite h.fixedField :=
    CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer.fixedField_finite h
  have hF : Nat.card K' = (2 ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  obtain ⟨P, hPk⟩ := exists_mul_antidiag_mul_transpose_eq_one (k := h.fixedField)
    (n := 2 * 3 + 1) (i₀ := ⟨3, by omega⟩) (Fin.ext (by simp only [Fin.val_rev]))
  obtain ⟨ι', ⟨Pa⟩⟩ := hβ (oddBeta P hPk)
  set ι : K →+* K' := h.fixedField.subtype.comp (ι' : K →+* h.fixedField) with hιdef
  have hι : ∀ c, unitaryInvolution K' 2 f (ι c) = ι c := fun c => by
    rw [unitaryInvolution_apply, ← h.bar_apply]
    exact h.mem_fixedField.1 (ι' c).2
  exact commute_pieceCore_zero_two_of_ctuParam hcat hdet (oddCentralSplit_siegelLevi (by norm_num))
    hset hKc hf e htC ht hF
    (ctuParamOfUnitaryOdd (hι := hι) (RingEquiv.refl K') (fun _ => rfl) P hPk Pa)
    (ctuParamOfUnitaryOdd_conj (hι := hι) (unitaryInvolution_involutive hF) _ _ P hPk Pa)

theorem spUnitaryOddFourOrthInput_of_catalogue
    (hcat : LinearPilot.SLmCatalogueClausesAt 4) : SpUnitaryOddFourOrthInput :=
  spUnitaryOddFourOrthInput_of_clauses hcat (LinearPilot.slmEvenTypeDetAt (by norm_num))

theorem spUnitaryOddParamCTInput_of_catalogue
    (hcat : LinearPilot.SLmCatalogueClausesAt 4) : SpUnitaryOddParamCTInput :=
  spUnitaryOddParamCTInput_of_orth (spUnitaryOddFourOrthInput_of_catalogue hcat)

end CFSG.SeitzReduction.SymplecticPilot
