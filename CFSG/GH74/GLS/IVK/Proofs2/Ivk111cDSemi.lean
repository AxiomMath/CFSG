module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GH74.GLS.Stage4.T2SL2Defs

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open scoped TensorProduct MonoidAlgebra

section Ring

instance mix11cD_ringHomInvPair {R : Type*} [Ring R] (ψ : R ≃+* R) :
    RingHomInvPair (ψ : R →+* R) (ψ.symm : R →+* R) :=
  RingHomInvPair.of_ringEquiv ψ

instance mix11cD_ringHomInvPair_symm {R : Type*} [Ring R] (ψ : R ≃+* R) :
    RingHomInvPair (ψ.symm : R →+* R) (ψ : R →+* R) :=
  RingHomInvPair.of_ringEquiv_symm ψ

variable {F G X Y : Type*} [Field F] [Group G] [AddCommGroup X] [Module F X] [AddCommGroup Y]
  [Module F Y] (ρ : Representation F G X) (π : Representation F G Y) (φ : F ≃+* F)

@[expose] noncomputable def gaTwist : F[G] ≃+* F[G] := MonoidAlgebra.mapRingEquiv G φ

theorem gaTwist_single (g : G) (c : F) :
    gaTwist (G := G) φ (MonoidAlgebra.single g c) = MonoidAlgebra.single g (φ c) :=
  MonoidAlgebra.mapRingEquiv_single φ c g

@[expose] noncomputable def semilinOfFrob (Θ : X ≃+ Y) (hs : ∀ (c : F) x, Θ (c • x) = φ c • Θ x)
    (hg : ∀ g x, Θ (ρ g x) = π g (Θ x)) :
    ρ.asModule ≃ₛₗ[((gaTwist (G := G) φ : F[G] ≃+* F[G]) : F[G] →+* F[G])] π.asModule where
  toFun x := π.asModuleEquiv.symm (Θ (ρ.asModuleEquiv x))
  map_add' x y := by simp [map_add]
  map_smul' r x := by
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [add_smul, map_add, ha, hb]
    | single g a =>
      have h1 : ((gaTwist (G := G) φ : F[G] →+* F[G])) (MonoidAlgebra.single g a) =
          MonoidAlgebra.single g (φ a) := gaTwist_single φ g a
      rw [h1, Representation.single_smul, Representation.single_smul]
      have key : Θ (a • ρ g (ρ.asModuleEquiv x)) = φ a • π g (Θ (ρ.asModuleEquiv x)) := by
        rw [hs, hg]
      exact key
  invFun y := ρ.asModuleEquiv.symm (Θ.symm (π.asModuleEquiv y))
  left_inv x := by simp
  right_inv y := by simp

end Ring

section Transport

variable {R : Type*} [Ring R] (ψ : R ≃+* R)
  {M P Q : Type*} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P] [AddCommGroup Q]
  [Module R Q]

@[expose] noncomputable def twistTransport (Φ : M ≃ₛₗ[(ψ : R →+* R)] M) (Θ : P ≃ₛₗ[(ψ : R →+* R)] Q)
    (N : Submodule R M) (ι : N ≃ₗ[R] P) : N.map Φ.toLinearMap ≃ₗ[R] Q :=
  let E1 : N ≃ₛₗ[(ψ : R →+* R)] N.map Φ.toLinearMap :=
    N.equivMapOfInjective Φ.toLinearMap Φ.injective
  (E1.symm.trans ι).trans Θ

end Transport

end CFSG.GH74.GLS.Stage4.Rest
