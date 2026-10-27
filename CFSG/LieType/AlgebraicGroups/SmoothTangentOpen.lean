module

public import CFSG.LieType.AlgebraicGroups.AffinePointGeometry
public import CFSG.LieType.AlgebraicGroups.SmoothTangentLocal
public import CFSG.LieType.AlgebraicGroups.TangentSpace
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.Spectrum.Prime.Chevalley

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

section TangentDerivation

variable {k A : Type} [Field k] [CommRing A] [Algebra k A] [Algebra A k]

@[expose] def derivationToTangent (x : A →ₐ[k] k) (hx : ∀ a, algebraMap A k a = x a)
    (D : Derivation k A k) : TangentSpace k A x :=
  ⟨D.toLinearMap, fun a b => by
    simp only [Derivation.coeFn_coe, Derivation.leibniz, Algebra.smul_def, hx]⟩

theorem coe_derivationToTangent (x : A →ₐ[k] k) (hx : ∀ a, algebraMap A k a = x a)
    (D : Derivation k A k) :
    ((derivationToTangent x hx D : tangentSpace k A x) : A →ₗ[k] k) = D.toLinearMap :=
  rfl

theorem derivationToTangent_bijective (x : A →ₐ[k] k) (hx : ∀ a, algebraMap A k a = x a) :
    Function.Bijective (derivationToTangent x hx) := by
  constructor
  · intro D₁ D₂ h
    ext a
    exact congrArg (fun T : TangentSpace k A x => (T : A →ₗ[k] k) a) h
  · intro T
    refine ⟨Derivation.mk' T.1 fun a b => ?_, rfl⟩
    rw [Algebra.smul_def, Algebra.smul_def, hx, hx]
    exact T.2 a b

end TangentDerivation

section Local

variable {k A B : Type} [Field k] [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
  [Algebra B A] [IsScalarTower k B A]

theorem isEtaleAt_ker_of_bijective_tangentMap [Algebra.FiniteType k A]
    [Algebra.FormallySmooth k A] [Algebra.FiniteType k B] (φ : B →ₐ[k] A)
    (hφ : ∀ b, algebraMap B A b = φ b) (x : A →ₐ[k] k) [(RingHom.ker x).IsPrime]
    (h : Function.Bijective (tangentMap φ (rfl : x.comp φ = x.comp φ))) :
    Algebra.IsEtaleAt B (RingHom.ker x) := by
  set P := RingHom.ker x
  let L := Localization.AtPrime P
  have hunit : ∀ s : P.primeCompl, IsUnit (x s) := fun s => isUnit_iff_ne_zero.2 s.2
  let xL : L →ₐ[k] k := IsLocalization.liftAlgHom (M := P.primeCompl) (f := x) hunit
  have hxL : ∀ a, xL (algebraMap A L a) = x a := fun a => IsLocalization.lift_eq _ a
  let : Algebra L k := (xL : L →+* k).toAlgebra
  let : Algebra A k := ((algebraMap L k).comp (algebraMap A L)).toAlgebra
  let : Algebra B k := ((algebraMap L k).comp (algebraMap B L)).toAlgebra
  have : IsScalarTower A L k := .of_algebraMap_eq' rfl
  have : IsScalarTower B L k := .of_algebraMap_eq' rfl
  have : IsScalarTower k L k := .of_algebraMap_eq fun c => (xL.commutes c).symm
  have : IsScalarTower k A k := IsScalarTower.to₁₂₄ k A L k
  have : IsScalarTower k B k := IsScalarTower.to₁₂₄ k B L k
  have hx : ∀ a, algebraMap A k a = x a := hxL
  have hy : ∀ b, algebraMap B k b = (x.comp φ) b := fun b => by
    change xL (algebraMap B L b) = x (φ b)
    rw [IsScalarTower.algebraMap_apply B A L, hxL, hφ]
  have : IsScalarTower B A k := .of_algebraMap_eq fun b => by
    rw [hy, hx, hφ]
    rfl
  have hAB : Function.Bijective fun D : Derivation k A k => D.compAlgebraMap B := by
    have hsq : derivationToTangent _ hy ∘ (fun D : Derivation k A k => D.compAlgebraMap B) =
        tangentMap φ rfl ∘ derivationToTangent x hx := by
      funext D
      refine Subtype.ext (LinearMap.ext fun b => ?_)
      simp [derivationToTangent, coe_tangentMap, Derivation.compAlgebraMap_apply, hφ]
    have h' := h.comp (derivationToTangent_bijective x hx)
    rw [← hsq] at h'
    exact (Function.Bijective.of_comp_iff' (derivationToTangent_bijective _ hy) _).1 h'
  have h1 : Function.Bijective fun D : Derivation k L k => D.compAlgebraMap B := by
    have hLA := bijective_compAlgebraMap_of_isLocalization k A L k P.primeCompl
    have : (fun D : Derivation k L k => D.compAlgebraMap B) =
        (fun D : Derivation k A k => D.compAlgebraMap B) ∘
          fun D : Derivation k L k => D.compAlgebraMap A := by
      funext D
      ext b
      simp [IsScalarTower.algebraMap_apply B A L]
    rw [this]
    exact hAB.comp hLA
  have h2 := bijective_baseChange_mapBaseChange_of_bijective_compAlgebraMap k B L k h1
  have hK : IsLocalRing.maximalIdeal L ≤ RingHom.ker (algebraMap L k) := by
    have : (RingHom.ker (algebraMap L k)).IsMaximal :=
      RingHom.ker_isMaximal_of_surjective _ fun c => ⟨algebraMap k L c, xL.commutes c⟩
    rw [IsLocalRing.eq_maximalIdeal this]
  have : Module.Free L Ω[L⁄k] := Module.free_of_flat_of_isLocalRing
  have h3 := bijective_of_bijective_lTensor_of_isLocalRing hK
    (KaehlerDifferential.mapBaseChange k B L) (by rwa [← LinearMap.baseChange_eq_ltensor])
  have : Subsingleton (Algebra.H1Cotangent k L) :=
    ((Algebra.formallySmooth_iff k L).1 inferInstance).2
  exact formallyEtale_of_bijective_mapBaseChange k B L h3

end Local

theorem exceptional_Lang_smooth_tangent_isomorphism_open {k : Type} [Field k] [IsAlgClosed k]
    {A B : Type} [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [Algebra.Smooth k A]
    [CommRing B] [Algebra k B] [Algebra.FiniteType k B] [Algebra.Smooth k B]
    (φ : B →ₐ[k] A) :
    (∀ x : A →ₐ[k] k, Function.Bijective (tangentMap φ (rfl : x.comp φ = x.comp φ)) →
      ∃ s : A, x s ≠ 0 ∧
        ((algebraMap A (Localization.Away s)).comp (φ : B →+* A)).Etale ∧
        IsOpenMap (PrimeSpectrum.comap
          ((algebraMap A (Localization.Away s)).comp (φ : B →+* A)))) ∧
    ((∀ x : A →ₐ[k] k, Function.Bijective (tangentMap φ (rfl : x.comp φ = x.comp φ))) →
      (φ : B →+* A).Etale ∧ IsOpenMap (PrimeSpectrum.comap (φ : B →+* A)) ∧
      ∃ U : Set (PrimeSpectrum B), IsOpen U ∧
        {y : B →ₐ[k] k | ∃ x : A →ₐ[k] k, x.comp φ = y} =
          {y | (⟨RingHom.ker y, RingHom.ker_isPrime y⟩ : PrimeSpectrum B) ∈ U}) := by
  let : Algebra B A := (φ : B →+* A).toAlgebra
  have hφ : ∀ b, algebraMap B A b = φ b := fun _ => rfl
  have : IsScalarTower k B A := .of_algebraMap_eq fun c => (φ.commutes c).symm
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  have : Algebra.FiniteType B A := Algebra.FiniteType.of_restrictScalars_finiteType k B A
  have : Algebra.FinitePresentation B A := Algebra.FinitePresentation.of_finiteType.1 inferInstance
  have hloc : ∀ x : A →ₐ[k] k, Function.Bijective (tangentMap φ (rfl : x.comp φ = x.comp φ)) →
      (⟨RingHom.ker x, RingHom.ker_isPrime x⟩ : PrimeSpectrum A) ∈ Algebra.etaleLocus B A := by
    intro x hx
    have := RingHom.ker_isPrime x
    exact isEtaleAt_ker_of_bijective_tangentMap φ hφ x hx
  have hopen : ∀ (C : Type) [CommRing C] [Algebra B C] [Algebra.Etale B C],
      IsOpenMap (PrimeSpectrum.comap (algebraMap B C)) := fun _ _ _ _ =>
    PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation
  refine ⟨fun x hx => ?_, fun hall => ?_⟩
  · have := RingHom.ker_isPrime x
    have : Algebra.IsEtaleAt B (RingHom.ker x) := hloc x hx
    obtain ⟨s, hs, hét⟩ := Algebra.exists_etale_of_isEtaleAt (R := B) (RingHom.ker x)
    have heq : (algebraMap A (Localization.Away s)).comp (φ : B →+* A) =
        algebraMap B (Localization.Away s) := (IsScalarTower.algebraMap_eq B A _).symm
    refine ⟨s, hs, ?_, ?_⟩
    · rw [heq]
      exact RingHom.etale_algebraMap.2 hét
    · rw [heq]
      exact hopen _
  ·
    have hét : Algebra.Etale B A := by
      rw [← Algebra.etaleLocus_eq_univ_iff_etale]
      refine Set.eq_univ_of_forall fun p => ?_
      obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p.asIdeal p.isPrime.ne_top
      obtain ⟨x, hx⟩ := exists_algHom_ker_eq k A m
      have hspec : p ⤳ (⟨RingHom.ker x, RingHom.ker_isPrime x⟩ : PrimeSpectrum A) := by
        rw [← PrimeSpectrum.le_iff_specializes]
        change p.asIdeal ≤ RingHom.ker x
        rw [hx]
        exact hpm
      exact hspec.mem_open Algebra.isOpen_etaleLocus (hloc x (hall x))
    refine ⟨RingHom.etale_algebraMap.2 hét, hopen A,
      Set.range (PrimeSpectrum.comap (φ : B →+* A)), (hopen A).isOpen_range, ?_⟩
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨⟨RingHom.ker x, RingHom.ker_isPrime x⟩, PrimeSpectrum.ext ?_⟩
      ext b
      simp [RingHom.mem_ker]
    ·
      rintro ⟨q, hq⟩
      have hle : Ideal.map (φ : B →+* A) (RingHom.ker y) ≤ q.asIdeal := by
        rw [Ideal.map_le_iff_le_comap]
        have := congrArg PrimeSpectrum.asIdeal hq
        rw [PrimeSpectrum.comap_asIdeal] at this
        rw [this]
      obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal _ (ne_top_of_le_ne_top q.isPrime.ne_top hle)
      obtain ⟨x, hx⟩ := exists_algHom_ker_eq k A m
      refine ⟨x, AlgHom.ext fun b => ?_⟩
      have hb : b - algebraMap k B (y b) ∈ RingHom.ker y := by simp [RingHom.mem_ker]
      have : φ (b - algebraMap k B (y b)) ∈ RingHom.ker x := by
        rw [hx]
        exact hIm (Ideal.mem_map_of_mem _ hb)
      rw [RingHom.mem_ker, map_sub, map_sub, AlgHom.commutes, AlgHom.commutes,
        Algebra.algebraMap_self, RingHom.id_apply, sub_eq_zero] at this
      exact this

end CFSG.LieType.AlgebraicGroups
