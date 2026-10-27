module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeUSevenStdSiegel
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeUSevenSiegel

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive unitaryInvolution_apply)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical (matrixIsometryGroup)
open CFSG.QuasithinUnique.Lin2.Five (tauSp)
open CFSG.SeitzReduction.F4Pilot (statedSpMap centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Witt

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]

theorem spThreeUOddNormalized_of_witt {f : ℕ} {e : L ≃* StatedSp 3 K} {t : G} {k : Fin 3}
    {K' : Type} [Field K'] (h : UnitaryFieldData 2 f K') [CharP h.fixedField 2]
    [Finite h.fixedField] {C₀ : GL (Fin (2 * 2 + 1)) K'} (hC : IsPrimeFormGram C₀)
    (hC₀ : ((C₀ : GL (Fin (2 * 2 + 1)) K') : Matrix (Fin (2 * 2 + 1)) (Fin (2 * 2 + 1)) K') = 1)
    (P : GL (Fin (2 * 2 + 1)) h.fixedField)
    (hP : ((P : GL (Fin (2 * 2 + 1)) h.fixedField) :
      Matrix (Fin (2 * 2 + 1)) (Fin (2 * 2 + 1)) h.fixedField) * antidiag (2 * 2 + 1) *
        ((P : GL (Fin (2 * 2 + 1)) h.fixedField) :
          Matrix (Fin (2 * 2 + 1)) (Fin (2 * 2 + 1)) h.fixedField)ᵀ = 1)
    (ι' : K ≃+* h.fixedField) (b : Bool)
    (Φ : gramSU h (C₀ : Matrix (Fin (2 * 2 + 1)) (Fin (2 * 2 + 1)) K') →* G)
    (hrange : Φ.range = neighbourCore e k)
    (hker : Φ.ker ≤ center (gramSU h (C₀ : Matrix (Fin (2 * 2 + 1)) (Fin (2 * 2 + 1)) K')))
    (hN1 : ∀ x : StatedSp 2 K,
      Φ (isoOneToSU h hC₀ (oddBeta P hP (statedSpMap (ι' : K →+* h.fixedField) 2
        (cond b (tauSp x) x)))) =
          ((e.symm ((complSpEquiv k x : complSp K k) : StatedSp 3 K) : L) : G))
    (hN3 : ∀ x, t * Φ x * t⁻¹ = Φ (primeFormFieldSU h hC (UnitaryPilot.barRingEquiv h) x)) :
    SpThreeUOddNormalized e t f k b := by
  have : Finite K' := h.finite
  have : CharP K' 2 := h.charP
  have hF : Nat.card K' = (2 ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  set ι : K →+* K' := h.fixedField.subtype.comp (ι' : K →+* h.fixedField) with hιdef
  have hι : ∀ c, unitaryInvolution K' 2 f (ι c) = ι c := fun c => by
    rw [unitaryInvolution_apply, ← h.bar_apply]
    exact (h.mem_fixedField.1 (ι' c).2)
  set E := ctuOddGramEquiv h hC₀ (RingEquiv.refl K') P hP with hE
  refine ⟨K', inferInstance, inferInstance, inferInstance, hF, ι, hι, Φ.comp E.toMonoidHom,
    ?_, fun x hx => mem_center_of_mulEquiv_mem_center E (hker hx), fun x => ?_, fun y => ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulEquiv.surjective _),
      ← MonoidHom.range_eq_map, hrange]
  · change Φ (E (ctuEmbed 1 le_rfl (unitaryInvolution K' 2 f) ι hι (cond b (tauSp x) x))) = _
    rw [hE, ctuOddGramEquiv_ctuEmbed h hC₀ (RingEquiv.refl K') P hP hι ι' (fun _ => rfl)]
    exact hN1 x
  · change t * Φ (E y) * t⁻¹ = Φ (E _)
    rw [hN3, hE, ctuOddGramEquiv_ctuaBarAut h hC₀ hC P hP hF]

variable [Finite G] [Finite K]

theorem exists_unitaryOddNeighbourParam_of_uodd_standard
    {f : ℕ}
    (hset : SeitzSetting G L) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp 3 K) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (k : Fin 3) (hk : RootKindSp e t f k .unitaryOdd) (hstd : SpThreeUOddStandard e) :
    ∃ (K' : Type) (_ : Field K') (h : UnitaryFieldData 2 f K') (_ : CharP h.fixedField 2)
      (_ : Finite h.fixedField) (C₀ : GL (Fin (2 * 2 + 1)) K') (hC : IsPrimeFormGram C₀)
      (hC₀ : ((C₀ : GL (Fin (2 * 2 + 1)) K') :
        Matrix (Fin (2 * 2 + 1)) (Fin (2 * 2 + 1)) K') = 1)
      (P : GL (Fin (2 * 2 + 1)) h.fixedField)
      (hP : ((P : GL (Fin (2 * 2 + 1)) h.fixedField) :
        Matrix (Fin (2 * 2 + 1)) (Fin (2 * 2 + 1)) h.fixedField) * antidiag (2 * 2 + 1) *
          ((P : GL (Fin (2 * 2 + 1)) h.fixedField) :
            Matrix (Fin (2 * 2 + 1)) (Fin (2 * 2 + 1)) h.fixedField)ᵀ = 1)
      (ι : K ≃+* h.fixedField),
      Nonempty (UnitaryOddNeighbourParam (m := 2) h e t k hC hC₀ (oddBeta P hP) ι) := by
  obtain ⟨K', _, h, _, C₀, hC, hC₀, hβ⟩ :=
    exists_unitaryOddNeighbourParam_three hset hKc hf e htC ht k hk
  have : Finite K' := h.finite
  have : CharP K' 2 := h.charP
  have : Finite h.fixedField :=
    CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer.fixedField_finite h
  obtain ⟨P, hP⟩ := exists_mul_antidiag_mul_transpose_eq_one (k := h.fixedField)
    (n := 2 * 2 + 1) (i₀ := ⟨2, by omega⟩) (Fin.ext (by simp only [Fin.val_rev]))
  obtain ⟨ι', κ, Φ, hκ, hrange, hker, hN1, hN3⟩ := hβ (oddBeta P hP)
  rcases hκ with rfl | rfl
  · exact ⟨K', inferInstance, h, inferInstance, inferInstance, C₀, hC, hC₀, P, hP, ι',
      ⟨{ Φ := Φ, range_eq := hrange, ker_le := hker, N1 := hN1, N3 := hN3 }⟩⟩
  · exact absurd (sq_add_one_dvd_natCard_edgeCoreSp_of_uodd_twisted hKc hf
      (spThreeUOddNormalized_of_witt h hC hC₀ P hP ι' true Φ hrange hker (fun x => hN1 x) hN3))
      (hstd k _ (ne_succAbove_zero_three k))

end Witt

section Ctu

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem exists_ctuParam_three_of_uodd_standard
    {f : ℕ}
    (hset : SeitzSetting G L) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp 3 K) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hroot : ∀ k : Fin 3, RootKindSp e t f k .unitaryOdd) (hstd : SpThreeUOddStandard e) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (_ : Nat.card F = (2 ^ f) ^ 2)
      (ι : K →+* F) (hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c),
      ∀ k : Fin 3, Nonempty (CtuParam 1 le_rfl (unitaryInvolution F 2 f) ι hι e k) := by
  obtain ⟨K₀', _, h₀, _, _, C₀, hC, hC₀, P₀, hP₀, ι₀, -⟩ :=
    exists_unitaryOddNeighbourParam_of_uodd_standard hset hKc hf e htC ht 0 (hroot 0) hstd
  have : Finite K₀' := h₀.finite
  have : CharP K₀' 2 := h₀.charP
  have hF : Nat.card K₀' = (2 ^ f) ^ 2 := by rw [h₀.card, ← pow_mul, mul_comm]
  set ι : K →+* K₀' := h₀.fixedField.subtype.comp (ι₀ : K →+* h₀.fixedField) with hιdef
  have hι : ∀ c, unitaryInvolution K₀' 2 f (ι c) = ι c := fun c => by
    rw [unitaryInvolution_apply, ← h₀.bar_apply]
    exact (h₀.mem_fixedField.1 (ι₀ c).2)
  refine ⟨K₀', inferInstance, inferInstance, inferInstance, hF, ι, hι, fun k => ?_⟩
  obtain ⟨K', _, h, _, _, C, hCk, hCk₀, P, hPk, ι', ⟨Pa⟩⟩ :=
    exists_unitaryOddNeighbourParam_of_uodd_standard hset hKc hf e htC ht k (hroot k) hstd
  have : Finite K' := h.finite
  obtain ⟨θ, hθ⟩ := exists_ringEquiv_comp_eq ι
    (h.fixedField.subtype.comp (ι' : K →+* h.fixedField))
    (by rw [hF, h.card, ← pow_mul, mul_comm])
  exact ⟨ctuParamOfUnitaryOdd θ hθ P hPk Pa⟩

end Ctu

@[expose] def SpThreeUnitaryOddCTInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 2 ≤ f →
    ∀ (e : L ≃* StatedSp 3 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin 3, RootKindSp e t f k .unitaryOdd) → SpThreeUOddStandard e →
      ∀ (F : Type) [Field F] [Finite F] [CharP F 2], Nat.card F = (2 ^ f) ^ 2 →
      ∀ (ι : K →+* F) (hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c),
        (∀ k : Fin 3, Nonempty (CtuParam 1 le_rfl (unitaryInvolution F 2 f) ι hι e k)) →
      ∀ (F' : Type) [Field F'] [Finite F'] (ι' : K →+* F') (σ' : F' ≃+* F'), σ' ≠ 1 →
        σ' * σ' = 1 → (∀ x : F', σ' x = x ↔ x ∈ Set.range ι') →
        Nonempty (SiegelFieldParam e t ι' σ') → SpGlobalCoverType e f .unitaryOdd

theorem spThreeUnitaryOddStandardInput_of_CT
    (hcat : LinearPilot.SLmCatalogueClausesAt 3) (hdet : LinearPilot.SLmEvenTypeDetAt 3)
    (hCT : SpThreeUnitaryOddCTInput) : SpThreeUnitaryOddStandardInput := by
  intro G _ _ L hset f K _ _ _ hKc hf e t hto hKt hroot hstd
  have htC : t ∈ centralizer (L : Set G) := by
    have h1 : t ∈ zpowers t := mem_zpowers t
    rw [← hKt] at h1
    exact h1.1
  obtain ⟨F, _, _, _, hF, ι, hι, hP⟩ :=
    exists_ctuParam_three_of_uodd_standard hset hKc hf e htC hto hroot hstd
  obtain ⟨F', _, _, ι', σ', hσ, hfix⟩ := exists_quadraticExtension K
  obtain ⟨hσ1, hσσ⟩ := ne_one_and_mul_self_of_orderOf_eq_two hσ
  exact hCT G L hset f K hKc hf e t hto hKt hroot hstd F hF ι hι hP F' ι' σ' hσ1 hσσ hfix
    (nonempty_siegelFieldParam_of_uodd_standard hcat hdet hset hKc hf e htC hto (hroot 2) hstd
      ι' hσ1 hσσ hfix)

theorem spThreeKindCoverInput_unitaryOdd_of_CT
    (hcat : LinearPilot.SLmCatalogueClausesAt 3) (hdet : LinearPilot.SLmEvenTypeDetAt 3)
    (hCT : SpThreeUnitaryOddCTInput) : SpThreeKindCoverInput .unitaryOdd :=
  spThreeKindCoverInput_unitaryOdd_of_clauses hcat hdet
    (spThreeUnitaryOddStandardInput_of_CT hcat hdet hCT)

end CFSG.SeitzReduction.SymplecticPilot
