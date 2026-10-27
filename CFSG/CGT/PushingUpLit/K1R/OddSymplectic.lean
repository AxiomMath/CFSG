module

public import CFSG.CGT.PushingUpLit.K1R.OddConfig
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatOddSymplectic
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatSporadicBase

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.GMSK.OddSymplectic

open Subgroup Module CFSG.Assembly.LowTwoRank
open LinearMap (BilinForm)
open CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueBAlternatingIsometry
open CFSG.ComponentClassification.CatalogueBSymplecticB
open CFSG.ComponentClassification.CatalogueBLinearTwoDescent
open CFSG.ComponentClassification.CatalogueBOrthogonalDescent
open CFSG.ComponentClassification.CatalogueBSymplecticRepresentation
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.SymplecticFourStandard
open CFSG.CGT.PushingUpLit.K1R (NoFourConfig)

namespace OddSymplecticInner

section Lift

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
  {B : LinearMap.BilinForm F V}

theorem exists_lift_noFour [Finite F] [FiniteDimensional F V] {K : Type*} [Field K]
    (φ : MulAut (isometryGroup B)) (hφZ : (scalarSigns B).map φ.toMonoidHom = scalarSigns B)
    (hφφ : ∀ g, φ (φ g) = g)
    (h : NoFourConfig (CatalogueBFixedCentralQuotient.onQuotient (scalarSigns B) φ hφZ) K) :
    ∃ Y : Subgroup (isometryGroup B), CFSG.Assembly.IsComponentOf Y (fixedSubgroup φ) ∧
      (∃ (A : Subgroup Y) (_ : A.Normal), (∀ a ∈ A, (a : isometryGroup B) ∈ scalarSigns B) ∧
        Nonempty (Y ⧸ A ≃* Matrix.SpecialLinearGroup (Fin 2) K)) ∧
      (∀ z₁ z₂ : isometryGroup B, (∀ y ∈ Y, y * z₁ = z₁ * y) → (∀ y ∈ Y, y * z₂ = z₂ * y) →
        z₁⁻¹ * φ z₁ ∈ scalarSigns B → z₂⁻¹ * φ z₂ ∈ scalarSigns B → z₁ * z₁ ∈ scalarSigns B →
        z₂ * z₂ ∈ scalarSigns B → z₁ * z₂ * (z₂ * z₁)⁻¹ ∈ scalarSigns B →
        z₁ ∉ scalarSigns B → z₂ ∉ scalarSigns B → z₁ * z₂⁻¹ ∉ scalarSigns B → False) := by
  classical
  set β := CatalogueBFixedCentralQuotient.onQuotient (scalarSigns B) φ hφZ with hβ
  obtain ⟨S, hSn, hSs, hSnab, ⟨eS⟩, hnf⟩ := h
  set X := S.map (fixedSubgroup β).subtype with hXdef
  have hX : CFSG.Assembly.IsComponentOf X (fixedSubgroup β) :=
    isComponentOf_map_subtype S hSn hSs hSnab
  have : Finite V := Module.finite_of_finite F
  have : Finite (V ≃ₗ[F] V) :=
    Finite.of_injective (fun g : V ≃ₗ[F] V => (g : V → V)) DFunLike.coe_injective
  obtain ⟨Y, hY, ⟨σY, hσYs, -, hσY⟩, -⟩ := OddClassSelector.central_lift (scalarSigns B)
    (scalarSigns_central B) φ hφZ hφφ hX
  set π := QuotientGroup.mk' (scalarSigns B)
  have hmem : ∀ z : isometryGroup B, (∀ y ∈ Y, y * z = z * y) → z⁻¹ * φ z ∈ scalarSigns B →
      π z ∈ fixedSubgroup β ⊓ centralizer (X : Set (projectiveSymplectic B)) := by
    intro z hzY hzφ
    refine mem_inf.mpr ⟨?_, ?_⟩
    · change β (π z) = π z
      rw [hβ, CatalogueBFixedCentralQuotient.onQuotient_mk]
      have h1 : π (z⁻¹ * φ z) = 1 := (QuotientGroup.eq_one_iff _).mpr hzφ
      rw [map_mul, map_inv, inv_mul_eq_one] at h1
      exact h1.symm
    · rw [mem_centralizer_iff]
      intro s hs
      obtain ⟨y, hy⟩ := hσYs ⟨s, hs⟩
      have hs' : s = (σY y : projectiveSymplectic B) := congrArg Subtype.val hy.symm
      rw [hs', hσY, ← map_mul, ← map_mul, hzY y y.2]
  have hπZ : ∀ z : isometryGroup B, π z = 1 ↔ z ∈ scalarSigns B := fun z =>
    QuotientGroup.eq_one_iff z
  refine ⟨Y, hY, ⟨σY.ker, inferInstance, fun a ha => ?_, ⟨?_⟩⟩, ?_⟩
  · have h1 : π (a : isometryGroup B) = 1 := by
      rw [← hσY a, ha]
      rfl
    exact (hπZ _).mp h1
  · exact (QuotientGroup.quotientKerEquivOfSurjective σY hσYs).trans
      ((S.equivMapOfInjective _ (Subgroup.subtype_injective _)).symm.trans eS)
  · intro z₁ z₂ hz₁ hz₂ hφ₁ hφ₂ h₁₁ h₂₂ hcomm hn₁ hn₂ hn₁₂
    rcases hnf _ (hmem z₁ hz₁ hφ₁) _ (hmem z₂ hz₂ hφ₂)
        (by rw [← map_mul]; exact (hπZ _).mpr h₁₁)
        (by rw [← map_mul]; exact (hπZ _).mpr h₂₂)
        (by
          have h1 := (hπZ _).mpr hcomm
          rw [map_mul, map_inv, mul_inv_eq_one] at h1
          rw [← map_mul, ← map_mul]
          exact h1) with h | h | h
    · exact hn₁ ((hπZ _).mp h)
    · exact hn₂ ((hπZ _).mp h)
    · exact hn₁₂ ((hπZ _).mp (by rw [map_mul, map_inv, h, mul_inv_cancel]))

end Lift

theorem statedSp_inner_false {F : Type} [Field F] [Finite F] {ℓ e : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e) (hF : Nat.card F = ℓ ^ e) {r : ℕ} (hr : 2 ≤ r) {K : Type*}
    [Field K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (α : MulAut (StatedProj (StatedSp r F))) (hα : orderOf α = 2)
    (hin : α ∈
      (MulAut.conj : StatedProj (StatedSp r F) →* MulAut (StatedProj (StatedSp r F))).range)
    (h : NoFourConfig α K) : False := by
  classical
  have : CharP F ℓ := finite_field_prime_power_characteristic hℓ he hF
  have hchar : ringChar F ≠ 2 := by rw [ringChar.eq F ℓ]; exact hℓ2
  have hr1 : 1 ≤ r := by omega
  have hαα : α * α = 1 := by rw [← sq, ← hα, pow_orderOf_eq_one]
  have hα1 : α ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hα
    omega
  obtain ⟨A, σ, hα', hσ2, ⟨d, hd⟩, hlin, -⟩ :=
    (odd_symplectic_automorphism_semilinear_representation hchar hr).2.2 α hαα hα1
  set μ := multiplierUnit A with hμdef
  have hμ := multiplierUnit_spec A
  have hBalt := SymplecticFlag.pairedSympForm_isAlt (K := F) (r := r)
  have hBnd := SymplecticFlag.pairedSympForm_nondegenerate (K := F) (r := r)
  have hdim := SymplecticFlag.finrank_standard (K := F) (r := r)
  by_cases hσ : σ = 1
  · subst hσ
    have hint : ∀ x, projectiveStatedEquiv hr1 (α x) =
        projectiveConjugation (pairedSympForm F r) (matrixLinIso (A : GL (Fin r ⊕ Fin r) F)) μ
          (matrix_similitude _ μ hμ) (projectiveStatedEquiv hr1 x) := by
      intro x
      rw [hα', map_one, mul_one]
      exact projectiveStatedEquiv_conjAut hr1 A μ hμ x
    have hsquare : ∀ x, matrixLinIso (A : GL (Fin r ⊕ Fin r) F)
        (matrixLinIso (A : GL (Fin r ⊕ Fin r) F) x) = (d : F) • x :=
      semilinearCoordMap_sq _ 1 hσ2 d hd
    have hinv : ∀ x, (matrixLinIso (A : GL (Fin r ⊕ Fin r) F)).symm
        ((matrixLinIso (A : GL (Fin r ⊕ Fin r) F)).symm x) = (d : F)⁻¹ • x := fun x => by
      rw [LinearEquiv.symm_apply_eq, LinearEquiv.symm_apply_eq, hsquare, smul_smul,
        mul_inv_cancel₀ (Units.ne_zero d), one_smul]
    have hφφ : ∀ g, similitudeConjugation (pairedSympForm F r)
        (matrixLinIso (A : GL (Fin r ⊕ Fin r) F)) μ (matrix_similitude _ μ hμ)
          (similitudeConjugation (pairedSympForm F r) (matrixLinIso (A : GL (Fin r ⊕ Fin r) F))
            μ (matrix_similitude _ μ hμ) g) = g := by
      intro g
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      rw [similitudeConjugation_apply, similitudeConjugation_apply, hinv, map_smul, hsquare,
        smul_smul, mul_inv_cancel₀ (Units.ne_zero d), one_smul]
    obtain ⟨Y, hY, ⟨Ak, _, hAZ, ⟨eQ⟩⟩, hfour⟩ := exists_lift_noFour _
      (scalarSigns_invariant _ _ μ (matrix_similitude _ μ hμ)) hφφ
      (h.of_mulEquiv (projectiveStatedEquiv hr1) hint)
    rw [fixed_similitudeConjugation_eq] at hY
    have hin' := hin
    rw [hα', map_one, mul_one] at hin'
    exact linear_case_rankOne_false hℓ hℓ2 he hF hr hdim hBalt hBnd _ d μ hsquare
      (matrix_similitude _ μ hμ) (matrixLinIso_ne_smul_one _ (hlin rfl)) hY Ak hAZ hn hK eQ
      hfour fun hμsq => (hμsq (exists_sq_eq_multiplierUnit_of_mem_range hr1 A hin')).elim
  · have hint : ∀ x, projectiveStatedEquiv hr1 (α x) =
        projectiveSemilinearConjugation (pairedSympForm F r) σ
          (semilinearCoordMap (A : GL (Fin r ⊕ Fin r) F) σ) μ (semilinearCoordMap_smul _ σ)
          (semilinearCoordMap_form _ σ μ hμ) (projectiveStatedEquiv hr1 x) := by
      intro x
      rw [hα']
      exact projectiveStatedEquiv_conjAut_fieldAut hr1 A σ μ hμ x
    have hsquare := semilinearCoordMap_sq (A : GL (Fin r ⊕ Fin r) F) σ hσ2 d hd
    have hinv : ∀ x, (semilinearCoordMap (A : GL (Fin r ⊕ Fin r) F) σ).symm
        ((semilinearCoordMap (A : GL (Fin r ⊕ Fin r) F) σ).symm x) = (d : F)⁻¹ • x :=
      fun x => by
        rw [AddEquiv.symm_apply_eq, AddEquiv.symm_apply_eq, hsquare, smul_smul,
          mul_inv_cancel₀ (Units.ne_zero d), one_smul]
    have hφφ : ∀ g, semilinearConjugation (pairedSympForm F r) σ
        (semilinearCoordMap (A : GL (Fin r ⊕ Fin r) F) σ) μ (semilinearCoordMap_smul _ σ)
          (semilinearCoordMap_form _ σ μ hμ) (semilinearConjugation (pairedSympForm F r) σ
            (semilinearCoordMap (A : GL (Fin r ⊕ Fin r) F) σ) μ (semilinearCoordMap_smul _ σ)
            (semilinearCoordMap_form _ σ μ hμ) g) = g := by
      intro g
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      rw [semilinearConjugation_apply, semilinearConjugation_apply, hinv, map_smul, hsquare,
        smul_smul, mul_inv_cancel₀ (Units.ne_zero d), one_smul]
    obtain ⟨Y, hY, ⟨Ak, _, hAZ, ⟨eQ⟩⟩, -⟩ := exists_lift_noFour _
      (semilinear_scalarSigns_invariant _ σ _ μ _ _) hφφ
      (h.of_mulEquiv (projectiveStatedEquiv hr1) hint)
    rw [fixed_semilinearConjugation_eq] at hY
    exact field_case_false hℓ hℓ2 he hF hr hdim hBalt hBnd σ hσ2 hσ _ μ d
      (semilinearCoordMap_smul _ σ) (semilinearCoordMap_form _ σ μ hμ) hsquare hY Ak hAZ hn hK eQ

end OddSymplecticInner

end CFSG.LocalAnalysis.EvenBN.GMSK.OddSymplectic

namespace CFSG.CGT.PushingUpLit.K1R

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.EvenBN.GMSK
open CFSG.LocalAnalysis.EvenBN.GMSK.OddSymplectic

theorem innerKernelSelector_oddSymplectic :
    InnerKernelSelector fun D _ => ∃ r p f : ℕ, p ≠ 2 ∧ LieModel D .PSp r p f := by
  refine InnerKernelSelector.of_false ?_
  intro D _ _ _ ⟨r, p, f, hp, hM⟩ n hn K _ _ hK α hα hin S hSα hSn hSK hnf
  obtain ⟨⟨hprime, hf, hr2, -⟩, F, _, _, hF, ⟨e⟩⟩ := statedClassicalModel_PSp_of_lieModel hM
  exact OddSymplecticInner.statedSp_inner_false hprime hp hf hF hr2 hn
    (by rw [Nat.card_eq_fintype_card, hK]) (MulAut.congr e α)
    (by rw [MulEquiv.orderOf_eq]; exact hα)
    ((CFSG.LocalAnalysis.EvenBN.GMSK.Sporadic.congr_mem_inner_iff e α).2 hin)
    ((noFourConfig_of_data hn hK hSα hSn hSK hnf).of_mulEquiv e fun x => by
      change e (α x) = e (α (e.symm (e x)))
      rw [MulEquiv.symm_apply_apply])

end CFSG.CGT.PushingUpLit.K1R
