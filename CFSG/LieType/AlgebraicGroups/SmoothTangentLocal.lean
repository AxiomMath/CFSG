module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Smooth.Local

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open TensorProduct

theorem formallyEtale_of_bijective_mapBaseChange (R S T : Type*) [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Subsingleton (Algebra.H1Cotangent R T)]
    (h : Function.Bijective (KaehlerDifferential.mapBaseChange R S T)) :
    Algebra.FormallyEtale S T := by
  rw [Algebra.formallyEtale_iff]
  constructor
  · refine ⟨fun a b => ?_⟩
    obtain ⟨a, rfl⟩ := KaehlerDifferential.map_surjective R S T a
    obtain ⟨b, rfl⟩ := KaehlerDifferential.map_surjective R S T b
    rw [(KaehlerDifferential.exact_mapBaseChange_map R S T a).2 (h.2 a),
      (KaehlerDifferential.exact_mapBaseChange_map R S T b).2 (h.2 b)]
  · have hδ : ∀ z : Algebra.H1Cotangent S T, z = 0 := fun z => by
      have h1 : Algebra.H1Cotangent.δ R S T z = 0 := h.1 (by
        rw [(Algebra.H1Cotangent.exact_δ_mapBaseChange R S T).apply_apply_eq_zero, map_zero])
      obtain ⟨w, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ R S T z).1 h1
      rw [Subsingleton.elim w 0, map_zero]
    exact ⟨fun a b => by rw [hδ a, hδ b]⟩

theorem bijective_of_bijective_lTensor_of_isLocalRing {L K M N : Type*} [CommRing L]
    [IsLocalRing L] [Field K] [Algebra L K]
    (hK : IsLocalRing.maximalIdeal L ≤ RingHom.ker (algebraMap L K))
    [AddCommGroup M] [Module L M] [AddCommGroup N] [Module L N]
    [Module.Finite L M] [Module.Finite L N] [Module.Free L N]
    (f : M →ₗ[L] N) (hf : Function.Bijective (f.lTensor K)) : Function.Bijective f := by
  let κ := IsLocalRing.ResidueField L
  let g : κ →ₐ[L] K := Ideal.Quotient.liftₐ _ (Algebra.ofId _ _) hK
  let := g.toAlgebra
  have : IsScalarTower L κ K := IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  have hconj : ⇑(f.lTensor K) =
      ⇑(AlgebraTensorModule.cancelBaseChange L κ K K N) ∘ ⇑((f.baseChange κ).lTensor K) ∘
        ⇑(AlgebraTensorModule.cancelBaseChange L κ K K M).symm := by
    funext t
    induction t with
    | tmul c m => simp
    | add t u ht hu => simp only [map_add, ht, hu, Function.comp_apply]
  have hinj : Function.Injective (f.lTensor κ) ↔ Function.Injective (f.lTensor K) := by
    rw [hconj, EquivLike.comp_injective, EquivLike.injective_comp,
      Module.FaithfullyFlat.lTensor_injective_iff_injective κ K (f.baseChange κ),
      LinearMap.baseChange_eq_ltensor]
  have hsurj : Function.Surjective (f.lTensor κ) ↔ Function.Surjective (f.lTensor K) := by
    rw [hconj, EquivLike.comp_surjective, EquivLike.surjective_comp,
      Module.FaithfullyFlat.lTensor_surjective_iff_surjective κ K (f.baseChange κ),
      LinearMap.baseChange_eq_ltensor]
  constructor
  · obtain ⟨l, hl⟩ :=
      (IsLocalRing.split_injective_iff_lTensor_residueField_injective f).2 (hinj.2 hf.1)
    exact Function.HasLeftInverse.injective ⟨l, LinearMap.congr_fun hl⟩
  · rw [← LinearMap.range_eq_top, ← IsLocalRing.map_tensorProduct_mk_eq_top,
      ← LinearMap.range_comp]
    have : TensorProduct.mk L κ N 1 ∘ₗ f = f.lTensor κ ∘ₗ TensorProduct.mk L κ M 1 := by
      ext
      simp
    rw [this, LinearMap.range_comp_of_range_eq_top, LinearMap.range_eq_top]
    · exact hsurj.2 hf.2
    · rw [LinearMap.range_eq_top]
      exact TensorProduct.mk_surjective L M κ Ideal.Quotient.mk_surjective

theorem liftKaehlerDifferential_restrictScalars_comp_map (R B L M : Type*) [CommRing R]
    [CommRing B] [CommRing L] [Algebra R B] [Algebra R L] [Algebra B L] [IsScalarTower R B L]
    [AddCommGroup M] [Module L M] [Module R M] [Module B M] [IsScalarTower R L M]
    [IsScalarTower B L M] [IsScalarTower R B M] (D : Derivation R L M) :
    D.liftKaehlerDifferential.restrictScalars B ∘ₗ KaehlerDifferential.map R R B L =
      (D.compAlgebraMap B).liftKaehlerDifferential := by
  refine Derivation.liftKaehlerDifferential_unique _ _ ?_
  ext b
  simp

theorem bijective_baseChange_mapBaseChange_of_bijective_compAlgebraMap (R B L K : Type*)
    [CommRing R] [CommRing B] [CommRing L] [Field K] [Algebra R B] [Algebra R L] [Algebra B L]
    [IsScalarTower R B L] [Algebra L K] [Algebra R K] [Algebra B K] [IsScalarTower R L K]
    [IsScalarTower B L K]
    (h : Function.Bijective fun D : Derivation R L K => D.compAlgebraMap B) :
    Function.Bijective ((KaehlerDifferential.mapBaseChange R B L).baseChange K) := by
  have : IsScalarTower R B K := IsScalarTower.to₁₂₄ R B L K
  set g := (KaehlerDifferential.mapBaseChange R B L).baseChange K
  let ΦL : Derivation R L K → Module.Dual K (K ⊗[L] Ω[L⁄R]) := fun D =>
    D.liftKaehlerDifferential.liftBaseChange K
  let ΦB : Derivation R B K → Module.Dual K (K ⊗[L] (L ⊗[B] Ω[B⁄R])) := fun E =>
    (E.liftKaehlerDifferential.liftBaseChange L).liftBaseChange K
  have hΦL : Function.Bijective ΦL :=
    (LinearMap.liftBaseChangeEquiv K).bijective.comp
      (KaehlerDifferential.linearMapEquivDerivation R L).symm.bijective
  have hΦB : Function.Bijective ΦB :=
    (LinearMap.liftBaseChangeEquiv K).bijective.comp <|
      (LinearMap.liftBaseChangeEquiv L).bijective.comp
        (KaehlerDifferential.linearMapEquivDerivation R B).symm.bijective
  have hsq : ⇑g.dualMap ∘ ΦL = ΦB ∘ fun D : Derivation R L K => D.compAlgebraMap B := by
    funext D
    have hD := liftKaehlerDifferential_restrictScalars_comp_map R B L K D
    refine LinearMap.ext fun t => ?_
    induction t with
    | add t u ht hu =>
      simp only [Function.comp_apply, map_add] at ht hu ⊢
      rw [ht, hu]
    | tmul c m =>
      induction m with
      | add m n hm hn =>
        simp only [Function.comp_apply, tmul_add, map_add] at hm hn ⊢
        rw [hm, hn]
      | tmul l ω =>
        simp only [Function.comp_apply, LinearMap.dualMap_apply, g, ΦL, ΦB,
          LinearMap.baseChange_tmul, KaehlerDifferential.mapBaseChange_tmul,
          LinearMap.liftBaseChange_tmul, map_smul, ← hD]
        rfl
  have hdual : Function.Bijective g.dualMap := by
    have := hΦB.comp h
    rw [← hsq] at this
    exact (Function.Bijective.of_comp_iff _ hΦL).1 this
  exact ⟨LinearMap.dualMap_surjective_iff.1 hdual.2, LinearMap.dualMap_injective_iff.1 hdual.1⟩

theorem bijective_compAlgebraMap_of_isLocalization (R A L M : Type*) [CommRing R] [CommRing A]
    [CommRing L] [Algebra R A] [Algebra R L] [Algebra A L] [IsScalarTower R A L]
    (S : Submonoid A) [IsLocalization S L]
    [AddCommGroup M] [Module L M] [Module A M] [Module R M] [IsScalarTower A L M]
    [IsScalarTower R L M] [IsScalarTower R A M] :
    Function.Bijective fun D : Derivation R L M => D.compAlgebraMap A := by
  constructor
  · intro D₁ D₂ h
    have h' : ∀ a, D₁ (algebraMap A L a) = D₂ (algebraMap A L a) := fun a =>
      Derivation.congr_fun h a
    ext z
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq S z
    have hs := IsLocalization.mk'_spec L a s
    have e₁ := congrArg D₁ hs
    have e₂ := congrArg D₂ hs
    rw [Derivation.leibniz] at e₁ e₂
    rw [← (IsLocalization.map_units L s).smul_left_cancel]
    have : algebraMap A L s • D₁ (IsLocalization.mk' L a s) =
        D₁ (algebraMap A L a) - IsLocalization.mk' L a s • D₁ (algebraMap A L s) := by
      rw [← e₁]
      abel
    rw [this, h', h', ← e₂]
    abel
  · intro E
    have : Algebra.FormallyEtale A L := Algebra.FormallyEtale.of_isLocalization S
    let ℓ : Ω[L⁄R] →ₗ[L] M := E.liftKaehlerDifferential.liftBaseChange L ∘ₗ
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A L).symm.toLinearMap
    refine ⟨ℓ.compDer (KaehlerDifferential.D R L), ?_⟩
    ext a
    simp [ℓ, KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]

end CFSG.LieType.AlgebraicGroups
