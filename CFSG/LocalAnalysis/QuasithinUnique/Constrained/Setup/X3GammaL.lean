module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderSemilinear

public section

namespace CFSG.QuasithinUnique.Setup.X3

open Equiv Subgroup CFSG.QuasithinUnique.Setup.Offender
open scoped LinearAlgebra.Projectivization

section Gamma

variable (F : Type*) [Field F] (V : Type*) [AddCommGroup V] [Module F V]

@[expose] def gammaL : Subgroup (Perm V) where
  carrier := {a | (∀ x y, a (x + y) = a x + a y) ∧ ∃ σ : F ≃+* F, IsSemilinearWith a σ}
  one_mem' := ⟨fun _ _ => rfl, 1, IsSemilinearWith.one_perm⟩
  mul_mem' := by
    rintro a b ⟨ha, σ, hσ⟩ ⟨hb, τ, hτ⟩
    exact ⟨fun x y => by simp [Perm.mul_apply, hb, ha], σ * τ, hσ.mul hτ⟩
  inv_mem' := by
    rintro a ⟨ha, σ, hσ⟩
    refine ⟨fun x y => ?_, σ.symm, ?_⟩
    · apply a.injective
      simp [ha]
    · intro c w
      apply a.injective
      have h1 : a (σ.symm c • a⁻¹ w) = σ (σ.symm c) • a (a⁻¹ w) := hσ _ _
      have h2 : a (a⁻¹ w) = w := a.apply_symm_apply w
      rw [h2, RingEquiv.apply_symm_apply] at h1
      exact (a.apply_symm_apply (c • w)).trans h1.symm

variable {F V}

theorem glToPerm_mem_gammaL (g : V ≃ₗ[F] V) : glToPerm g ∈ gammaL F V :=
  ⟨fun x y => map_add g x y, 1, fun c w => by simp [glToPerm_apply]⟩

end Gamma

section Points

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

theorem gammaL_map_zero {a : Perm V} (ha : a ∈ gammaL F V) : a 0 = 0 := by
  obtain ⟨σ, hσ⟩ := ha.2
  exact hσ.map_zero

theorem gammaL_ne_zero {a : Perm V} (ha : a ∈ gammaL F V) {v : V} (hv : v ≠ 0) : a v ≠ 0 := by
  intro h
  apply hv
  apply a.injective
  rw [h, gammaL_map_zero ha]

@[expose] noncomputable def pointAct (a : gammaL F V) : ℙ F V → ℙ F V :=
  Projectivization.lift (fun v => Projectivization.mk F (a.1 v.1) (gammaL_ne_zero a.2 v.2))
    (by
      intro u w t htw
      obtain ⟨σ, hσ⟩ := a.2.2
      rw [Projectivization.mk_eq_mk_iff']
      refine ⟨σ t, ?_⟩
      have h : (u : V) = t • (w : V) := htw
      show σ t • a.1 w.1 = a.1 u.1
      rw [h]
      exact (hσ t w.1).symm)

theorem pointAct_mk (a : gammaL F V) {v : V} (hv : v ≠ 0) :
    pointAct a (Projectivization.mk F v hv) =
      Projectivization.mk F (a.1 v) (gammaL_ne_zero a.2 hv) := rfl

theorem pointAct_one (x : ℙ F V) : pointAct (1 : gammaL F V) x = x := by
  induction x with | h v hv => rfl

theorem pointAct_mul (a b : gammaL F V) (x : ℙ F V) :
    pointAct (a * b) x = pointAct a (pointAct b x) := by
  induction x with | h v hv => rfl

@[expose] noncomputable def pointActHom : gammaL F V →* Perm (ℙ F V) where
  toFun a :=
    { toFun := pointAct a
      invFun := pointAct a⁻¹
      left_inv := fun x => by rw [← pointAct_mul, inv_mul_cancel, pointAct_one]
      right_inv := fun x => by rw [← pointAct_mul, mul_inv_cancel, pointAct_one] }
  map_one' := Equiv.ext fun x => pointAct_one x
  map_mul' a b := Equiv.ext fun x => pointAct_mul a b x

@[expose] def scalarHom (F : Type*) [Field F] (V : Type*) [AddCommGroup V] [Module F V] :
    Fˣ →* (V ≃ₗ[F] V) where
  toFun c := LinearEquiv.smulOfUnit c
  map_one' := LinearEquiv.ext fun _ => one_smul _ _
  map_mul' c d := LinearEquiv.ext fun v => mul_smul c d v

theorem scalarHom_apply (c : Fˣ) (v : V) : scalarHom F V c v = c • v := rfl

theorem pointAct_scalar (c : Fˣ) (x : ℙ F V) :
    pointAct ⟨glToPerm (scalarHom F V c), glToPerm_mem_gammaL _⟩ x = x := by
  induction x with
  | h _ hv =>
    rw [pointAct_mk, Projectivization.mk_eq_mk_iff F _ _ _ hv]
    exact ⟨c, rfl⟩

end Points

end CFSG.QuasithinUnique.Setup.X3
