module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Tangent
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Conjugation

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups.QuotientConjugation

open TauCeti WithConv

universe u v
variable {k : Type u} [CommRing k]
variable {H : Type v} [CommRing H] [HopfAlgebra k H]

@[expose] def coordinateHom (I : HopfIdeal k H) (g : WithConv (H →ₐ[k] k)) :
    (H ⧸ (I.conjugate g).toIdeal) →ₐc[k] (H ⧸ I.toIdeal) :=
  Bialgebra.Quotient.liftBialgHom (I.conjugate g).toIdeal
    ((Bialgebra.Quotient.mkBialgHom I.toIdeal).comp
      (TauCeti.HopfAlgebra.pointConjugationBialgEquiv g).toBialgHom)
    (by
      intro a ha
      change Ideal.Quotient.mk I.toIdeal
        (TauCeti.HopfAlgebra.pointConjugationBialgEquiv g a) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      have hm := HopfIdeal.mem_conjugate.mp ha
      change TauCeti.HopfAlgebra.pointConjugationBialgEquiv g a ∈ I
      simpa only [← TauCeti.HopfAlgebra.pointConjugationBialgEquiv_toAlgHom,
        BialgHom.coe_toAlgHom, BialgEquiv.coe_toBialgHom] using hm)

theorem coordinateHom_mk (I : HopfIdeal k H) (g : WithConv (H →ₐ[k] k)) (a : H) :
    coordinateHom I g (Ideal.Quotient.mk (I.conjugate g).toIdeal a) =
      Ideal.Quotient.mk I.toIdeal (TauCeti.HopfAlgebra.pointConjugationBialgEquiv g a) := by
  rw [coordinateHom, Bialgebra.Quotient.liftBialgHom_mk]
  rfl

theorem coordinateHom_bijective (I : HopfIdeal k H) (g : WithConv (H →ₐ[k] k)) :
    Function.Bijective (coordinateHom I g) := by
  constructor
  · intro x y h
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [coordinateHom_mk, coordinateHom_mk] at h
    apply Ideal.Quotient.eq.mpr
    change a - b ∈ I.conjugate g
    rw [HopfIdeal.mem_conjugate, map_sub]
    have hm := Ideal.Quotient.eq.mp h
    change TauCeti.HopfAlgebra.pointConjugationBialgEquiv g a -
      TauCeti.HopfAlgebra.pointConjugationBialgEquiv g b ∈ I at hm
    simpa only [← TauCeti.HopfAlgebra.pointConjugationBialgEquiv_toAlgHom,
      BialgHom.coe_toAlgHom, BialgEquiv.coe_toBialgHom] using hm
  · intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨Ideal.Quotient.mk (I.conjugate g).toIdeal
      ((TauCeti.HopfAlgebra.pointConjugationBialgEquiv g).symm a), ?_⟩
    rw [coordinateHom_mk, BialgEquiv.apply_symm_apply]

@[expose] def coordinateEquiv (I : HopfIdeal k H) (g : WithConv (H →ₐ[k] k)) :
    (H ⧸ (I.conjugate g).toIdeal) ≃ₐc[k] (H ⧸ I.toIdeal) :=
  BialgEquiv.ofBijective (coordinateHom I g) (coordinateHom_bijective I g)

theorem coordinateEquiv_mk (I : HopfIdeal k H) (g : WithConv (H →ₐ[k] k)) (a : H) :
    coordinateEquiv I g (Ideal.Quotient.mk (I.conjugate g).toIdeal a) =
      Ideal.Quotient.mk I.toIdeal (TauCeti.HopfAlgebra.pointConjugationBialgEquiv g a) :=
  coordinateHom_mk I g a

@[expose] def lieLinearEquiv (g : WithConv (H →ₐ[k] k)) :
    Derivation k H (Bialgebra.CounitAlgebra k H k) ≃ₗ[k]
      Derivation k H (Bialgebra.CounitAlgebra k H k) where
  toLinearMap := derivationComp (B := k)
    (TauCeti.HopfAlgebra.pointConjugationBialgEquiv g).toBialgHom
  invFun := derivationComp (B := k)
    (TauCeti.HopfAlgebra.pointConjugationBialgEquiv g).symm.toBialgHom
  left_inv d := by
    change derivationComp (B := k)
      (TauCeti.HopfAlgebra.pointConjugationBialgEquiv g).symm.toBialgHom
      (derivationComp (B := k)
        (TauCeti.HopfAlgebra.pointConjugationBialgEquiv g).toBialgHom d) = d
    apply Derivation.ext
    intro a
    rw [derivationComp_apply, derivationComp_apply]
    change d (TauCeti.HopfAlgebra.pointConjugationBialgEquiv g
      ((TauCeti.HopfAlgebra.pointConjugationBialgEquiv g).symm a)) = d a
    rw [BialgEquiv.apply_symm_apply]
  right_inv d := by
    change derivationComp (B := k)
      (TauCeti.HopfAlgebra.pointConjugationBialgEquiv g).toBialgHom
      (derivationComp (B := k)
        (TauCeti.HopfAlgebra.pointConjugationBialgEquiv g).symm.toBialgHom d) = d
    apply Derivation.ext
    intro a
    rw [derivationComp_apply, derivationComp_apply]
    change d ((TauCeti.HopfAlgebra.pointConjugationBialgEquiv g).symm
      (TauCeti.HopfAlgebra.pointConjugationBialgEquiv g a)) = d a
    rw [BialgEquiv.symm_apply_apply]

theorem lieLinearEquiv_apply (g : WithConv (H →ₐ[k] k))
    (d : Derivation k H (Bialgebra.CounitAlgebra k H k)) :
    lieLinearEquiv g d = derivationComp (B := k)
      (TauCeti.HopfAlgebra.pointConjugationBialgEquiv g).toBialgHom d := rfl

theorem lieLinearEquiv_mem_lieSubalgebra_iff (I : HopfIdeal k H)
    (g : WithConv (H →ₐ[k] k))
    (d : Derivation k H (Bialgebra.CounitAlgebra k H k)) :
    lieLinearEquiv g d ∈ (I.conjugate g).lieSubalgebra (B := k) ↔
      d ∈ I.lieSubalgebra (B := k) := by
  rw [HopfIdeal.mem_lieSubalgebra_iff, HopfIdeal.mem_lieSubalgebra_iff]
  constructor
  · intro hd a ha
    have hx : (TauCeti.HopfAlgebra.pointConjugationBialgEquiv g).symm a ∈ I.conjugate g := by
      rw [HopfIdeal.mem_conjugate]
      simpa only [← TauCeti.HopfAlgebra.pointConjugationBialgEquiv_toAlgHom,
        BialgHom.coe_toAlgHom, BialgEquiv.coe_toBialgHom,
        BialgEquiv.apply_symm_apply, HopfIdeal.mem_toIdeal] using ha
    have hz := hd _ hx
    rw [lieLinearEquiv_apply, derivationComp_apply] at hz
    change d (TauCeti.HopfAlgebra.pointConjugationBialgEquiv g
      ((TauCeti.HopfAlgebra.pointConjugationBialgEquiv g).symm a)) = 0 at hz
    rw [BialgEquiv.apply_symm_apply] at hz
    exact hz
  · intro hd a ha
    rw [lieLinearEquiv_apply, derivationComp_apply]
    change d (TauCeti.HopfAlgebra.pointConjugationBialgEquiv g a) = 0
    apply hd
    change TauCeti.HopfAlgebra.pointConjugationBialgEquiv g a ∈ I
    simpa only [← TauCeti.HopfAlgebra.pointConjugationBialgEquiv_toAlgHom,
      BialgHom.coe_toAlgHom, BialgEquiv.coe_toBialgHom] using HopfIdeal.mem_conjugate.mp ha

theorem lieSubalgebra_map (I : HopfIdeal k H) (g : WithConv (H →ₐ[k] k)) :
    (I.lieSubalgebra (B := k)).toSubmodule.map (lieLinearEquiv g).toLinearMap =
      ((I.conjugate g).lieSubalgebra (B := k)).toSubmodule := by
  ext d
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (lieLinearEquiv_mem_lieSubalgebra_iff I g x).mpr hx
  · intro hd
    refine ⟨(lieLinearEquiv g).symm d, ?_, (lieLinearEquiv g).apply_symm_apply d⟩
    apply (lieLinearEquiv_mem_lieSubalgebra_iff I g _).mp
    rw [LinearEquiv.apply_symm_apply]
    exact (LieSubalgebra.mem_toSubmodule
      (L' := (I.conjugate g).lieSubalgebra (B := k))).mp hd

@[expose] def lieQuotientEquiv (I : HopfIdeal k H) (g : WithConv (H →ₐ[k] k)) :
    (Derivation k H (Bialgebra.CounitAlgebra k H k) ⧸ (I.lieSubalgebra (B := k)).toSubmodule) ≃ₗ[k]
      (Derivation k H (Bialgebra.CounitAlgebra k H k) ⧸
        ((I.conjugate g).lieSubalgebra (B := k)).toSubmodule) :=
  Submodule.Quotient.equiv _ _ (lieLinearEquiv g) (lieSubalgebra_map I g)

theorem lieQuotientEquiv_mk (I : HopfIdeal k H) (g : WithConv (H →ₐ[k] k))
    (d : Derivation k H (Bialgebra.CounitAlgebra k H k)) :
    lieQuotientEquiv I g (Submodule.Quotient.mk d) =
      Submodule.Quotient.mk (lieLinearEquiv g d) := rfl

theorem coordinateEquiv_comp_mk (I : HopfIdeal k H) (g : WithConv (H →ₐ[k] k)) :
    (coordinateEquiv I g).toBialgHom.comp
        (Bialgebra.Quotient.mkBialgHom (I.conjugate g).toIdeal) =
      (Bialgebra.Quotient.mkBialgHom I.toIdeal).comp
        (TauCeti.HopfAlgebra.pointConjugationBialgEquiv g).toBialgHom := by
  ext a
  exact coordinateEquiv_mk I g a

theorem lieLinearEquiv_derivationComp_pointConjugation
    (g q : WithConv (H →ₐ[k] k))
    (d : Derivation k H (Bialgebra.CounitAlgebra k H k)) :
    lieLinearEquiv g (derivationComp (B := k)
        (TauCeti.HopfAlgebra.pointConjugationBialgEquiv q).toBialgHom d) =
      derivationComp (B := k)
        (TauCeti.HopfAlgebra.pointConjugationBialgEquiv (g * q * g⁻¹)).toBialgHom
        (lieLinearEquiv g d) := by
  have hcoord : (TauCeti.HopfAlgebra.pointConjugationAlgHom g).comp
      (TauCeti.HopfAlgebra.pointConjugationAlgHom (g * q * g⁻¹)) =
      (TauCeti.HopfAlgebra.pointConjugationAlgHom q).comp
        (TauCeti.HopfAlgebra.pointConjugationAlgHom g) := by
    rw [← TauCeti.HopfAlgebra.pointConjugationAlgHom_mul,
      ← TauCeti.HopfAlgebra.pointConjugationAlgHom_mul]
    congr 1
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  apply Derivation.ext
  intro a
  simp only [lieLinearEquiv_apply, derivationComp_apply]
  change d (TauCeti.HopfAlgebra.pointConjugationBialgEquiv q
      (TauCeti.HopfAlgebra.pointConjugationBialgEquiv g a)) =
    d (TauCeti.HopfAlgebra.pointConjugationBialgEquiv g
      (TauCeti.HopfAlgebra.pointConjugationBialgEquiv (g * q * g⁻¹) a))
  simpa only [AlgHom.comp_apply,
    ← TauCeti.HopfAlgebra.pointConjugationBialgEquiv_toAlgHom,
    BialgHom.coe_toAlgHom, BialgEquiv.coe_toBialgHom] using
    congrArg d (AlgHom.congr_fun hcoord a).symm

end CFSG.LieType.AlgebraicGroups.QuotientConjugation
