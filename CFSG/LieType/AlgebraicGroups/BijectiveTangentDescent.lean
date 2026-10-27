module

public import CFSG.LieType.AlgebraicGroups.AffinePointGeometry
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.Unramified.Basic

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

namespace BijectiveTangent

open TensorProduct

theorem surjective_comap_of_isOpenMap {k R B : Type} [Field k] [IsAlgClosed k] [CommRing R]
    [Algebra k R] [Algebra.FiniteType k R] [CommRing B] [Algebra k B] (φ : R →ₐ[k] B)
    (hopen : IsOpenMap (PrimeSpectrum.comap (φ : R →+* B)))
    (hsurj : ∀ y : R →ₐ[k] k, ∃ x : B →ₐ[k] k, x.comp φ = y) :
    Function.Surjective (PrimeSpectrum.comap (φ : R →+* B)) := by
  intro p
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p.asIdeal p.isPrime.ne_top
  obtain ⟨y, hy⟩ := exists_algHom_ker_eq k R m
  obtain ⟨x, rfl⟩ := hsurj y
  have hmem : (⟨m, hm.isPrime⟩ : PrimeSpectrum R) ∈
      Set.range (PrimeSpectrum.comap (φ : R →+* B)) := by
    refine ⟨⟨RingHom.ker x, RingHom.ker_isPrime x⟩, PrimeSpectrum.ext ?_⟩
    change Ideal.comap (φ : R →+* B) (RingHom.ker x) = m
    rw [← hy]
    ext r
    simp [RingHom.mem_ker]
  have hspec : p ⤳ (⟨m, hm.isPrime⟩ : PrimeSpectrum R) :=
    (PrimeSpectrum.le_iff_specializes _ _).1 hpm
  exact hspec.mem_open hopen.isOpen_range hmem

theorem injective_lmul'_of_injective_comp {k R B : Type} [Field k] [IsAlgClosed k] [CommRing R]
    [CommRing B] [Algebra k R] [Algebra k B] [Algebra R B] [IsScalarTower k R B]
    [Algebra.FiniteType k B] [Algebra.FormallyUnramified R B]
    (hinj : Function.Injective fun x : B →ₐ[k] k => x.comp (IsScalarTower.toAlgHom k R B)) :
    Function.Injective (Algebra.TensorProduct.lmul' R : B ⊗[R] B →ₐ[R] B) := by
  have : Algebra.FiniteType R B := Algebra.FiniteType.of_restrictScalars_finiteType k R B
  have : Algebra.FiniteType k (B ⊗[R] B) :=
    Algebra.FiniteType.trans (S := B) inferInstance inferInstance
  let I := KaehlerDifferential.ideal R B
  have hfg : I.FG := KaehlerDifferential.ideal_fg R B
  have hidem : IsIdempotentElem I :=
    (Ideal.cotangent_subsingleton_iff _).mp (inferInstanceAs (Subsingleton Ω[B⁄R]))
  have hjac : I ≤ Ideal.jacobson ⊥ := by
    rw [Ideal.jacobson, le_sInf_iff]
    rintro M ⟨-, hM⟩
    obtain ⟨z, hz⟩ := exists_algHom_ker_eq k (B ⊗[R] B) M
    rw [show I = _ from (KaehlerDifferential.span_range_eq_ideal R B).symm, Ideal.span_le, ← hz]
    rintro _ ⟨s, rfl⟩
    let x₁ : B →ₐ[k] k := z.comp (Algebra.TensorProduct.includeLeft (S := k))
    let x₂ : B →ₐ[k] k := z.comp (Algebra.TensorProduct.includeRight.restrictScalars k)
    have h12 : x₁ = x₂ := hinj (AlgHom.ext fun r => by
      change z (algebraMap R B r ⊗ₜ[R] 1) = z (1 ⊗ₜ[R] algebraMap R B r)
      rw [Algebra.TensorProduct.tmul_one_eq_one_tmul])
    have hs := DFunLike.congr_fun h12 s
    change z (s ⊗ₜ[R] 1) = z (1 ⊗ₜ[R] s) at hs
    simp [RingHom.mem_ker, hs]
  have hbot : I = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I I hfg
    (by rw [smul_eq_mul, hidem.eq]) hjac
  rw [injective_iff_map_eq_zero]
  intro t ht
  have : t ∈ I := ht
  rw [hbot] at this
  exact this

theorem bijective_algebraMap_of_injective_lmul' {R B : Type*} [CommRing R] [CommRing B]
    [Algebra R B] [Module.FaithfullyFlat R B]
    (h : Function.Injective (Algebra.TensorProduct.lmul' R : B ⊗[R] B →ₐ[R] B)) :
    Function.Bijective (algebraMap R B) := by
  refine ⟨(RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance).injective, ?_⟩
  have hsurj : Function.Surjective ((Algebra.linearMap R B).lTensor B) := by
    intro t
    refine ⟨Algebra.TensorProduct.lmul' R t ⊗ₜ 1, h ?_⟩
    simp
  exact (Module.FaithfullyFlat.lTensor_surjective_iff_surjective R B _).1 hsurj

end BijectiveTangent

end CFSG.LieType.AlgebraicGroups
