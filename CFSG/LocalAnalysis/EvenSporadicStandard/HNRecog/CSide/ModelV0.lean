module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.ModelF4
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

@[expose] public section

namespace CFSG.EvenSporadicStandard.HNRecog.CSide

open Matrix

abbrev SL2 : Type := Matrix.SpecialLinearGroup (Fin 2) F4

abbrev V0 : Type := Matrix (Fin 2) (Fin 2) F4

instance : Algebra (ZMod 2) F4 := ZMod.algebra F4 2

def actFun (g : SL2 × SL2) (M : V0) : V0 :=
  (g.1 : Matrix (Fin 2) (Fin 2) F4) * M * (g.2 : Matrix (Fin 2) (Fin 2) F4)ᵀ

theorem actFun_one (M : V0) : actFun 1 M = M := by
  simp [actFun]

theorem actFun_mul (g h : SL2 × SL2) (M : V0) :
    actFun (g * h) M = actFun g (actFun h M) := by
  simp only [actFun, Prod.fst_mul, Prod.snd_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.transpose_mul, Matrix.mul_assoc]

def actLinEquiv (g : SL2 × SL2) : V0 ≃ₗ[ZMod 2] V0 where
  toFun := actFun g
  map_add' M N := by
    simp [actFun, Matrix.mul_add, Matrix.add_mul]
  map_smul' c M := by
    simp [actFun, Matrix.mul_smul, Matrix.smul_mul]
  invFun := actFun g⁻¹
  left_inv M := by
    rw [← actFun_mul, inv_mul_cancel, actFun_one]
  right_inv M := by
    rw [← actFun_mul, mul_inv_cancel, actFun_one]

def act0 : SL2 × SL2 →* (V0 ≃ₗ[ZMod 2] V0) where
  toFun := actLinEquiv
  map_one' := by
    ext M : 1
    exact actFun_one M
  map_mul' g h := by
    ext M : 1
    exact actFun_mul g h M

theorem act0_apply (g : SL2 × SL2) (M : V0) : act0 g M = actFun g M := rfl

def det0 (M : V0) : F4 := M 0 0 * M 1 1 + M 0 1 * M 1 0

def q0Fun (M : V0) : ZMod 2 := (det0 M).b

def q0Polar (M N : V0) : ZMod 2 :=
  (M 0 0 * N 1 1 + N 0 0 * M 1 1 + M 0 1 * N 1 0 + N 0 1 * M 1 0).b

theorem tr_add (x y : F4) : (x + y).b = x.b + y.b := rfl

theorem q0Fun_add (M N : V0) : q0Fun (M + N) = q0Fun M + q0Fun N + q0Polar M N := by
  simp only [q0Fun, det0, q0Polar, Matrix.add_apply, mul_add, add_mul, tr_add]
  abel

theorem q0Fun_zero : q0Fun (0 : V0) = 0 := by
  simp [q0Fun, det0]
  rfl

theorem q0Fun_smul (c : ZMod 2) (M : V0) : q0Fun (c • M) = (c * c) • q0Fun M := by
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
  · simp [q0Fun_zero]
  · simp

theorem q0Polar_add_left (M M' N : V0) :
    q0Polar (M + M') N = q0Polar M N + q0Polar M' N := by
  simp only [q0Polar, Matrix.add_apply, mul_add, add_mul, tr_add]
  abel

theorem q0Polar_add_right (M N N' : V0) :
    q0Polar M (N + N') = q0Polar M N + q0Polar M N' := by
  simp only [q0Polar, Matrix.add_apply, mul_add, add_mul, tr_add]
  abel

theorem q0Polar_smul_left (c : ZMod 2) (M N : V0) :
    q0Polar (c • M) N = c • q0Polar M N := by
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
  · simp [q0Polar]
    rfl
  · simp

theorem q0Polar_smul_right (c : ZMod 2) (M N : V0) :
    q0Polar M (c • N) = c • q0Polar M N := by
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
  · simp [q0Polar]
    rfl
  · simp

def q0 : QuadraticForm (ZMod 2) V0 where
  toFun := q0Fun
  toFun_smul := q0Fun_smul
  exists_companion' :=
    ⟨LinearMap.mk₂ (ZMod 2) q0Polar q0Polar_add_left q0Polar_smul_left q0Polar_add_right
      q0Polar_smul_right, fun M N => q0Fun_add M N⟩

theorem q0_apply (M : V0) : q0 M = q0Fun M := rfl

theorem eq_zero_of_tr_mul (x : F4) (h : ∀ c : F4, (x * c).b = 0) : x = 0 := by
  revert x
  decide

theorem q0Polar_nondeg (M : V0) (h : ∀ N : V0, q0Polar M N = 0) : M = 0 := by
  have h00 : M 0 0 = 0 := eq_zero_of_tr_mul _ fun c => by
    have := h (Matrix.of fun i j => if i = 1 ∧ j = 1 then c else 0)
    simpa [q0Polar] using this
  have h11 : M 1 1 = 0 := eq_zero_of_tr_mul _ fun c => by
    have := h (Matrix.of fun i j => if i = 0 ∧ j = 0 then c else 0)
    simpa [q0Polar, mul_comm] using this
  have h01 : M 0 1 = 0 := eq_zero_of_tr_mul _ fun c => by
    have := h (Matrix.of fun i j => if i = 1 ∧ j = 0 then c else 0)
    simpa [q0Polar] using this
  have h10 : M 1 0 = 0 := eq_zero_of_tr_mul _ fun c => by
    have := h (Matrix.of fun i j => if i = 0 ∧ j = 1 then c else 0)
    simpa [q0Polar, mul_comm] using this
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]

theorem det0_eq (M : V0) : det0 M = M.det := by
  rw [Matrix.det_fin_two, det0, sub_eq_add_neg]
  rfl

theorem det0_actFun (g : SL2 × SL2) (M : V0) : det0 (actFun g M) = det0 M := by
  simp [det0_eq, actFun, Matrix.det_mul]

theorem q0_act0 (g : SL2 × SL2) (M : V0) : q0 (act0 g M) = q0 M := by
  change q0Fun (actFun g M) = q0Fun M
  simp [q0Fun, det0_actFun]

def frobFun (M : V0) : V0 := M.map F4.frob

def b0Fun (M : V0) : V0 := (frobFun M)ᵀ

def omegaFun (M : V0) : V0 := F4.omega • M

theorem frob_frob (x : F4) : F4.frob (F4.frob x) = x := by
  revert x
  decide

theorem frob_smul (c : ZMod 2) (x : F4) : F4.frob (c • x) = c • F4.frob x := by
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
  · simp
  · simp

theorem b0Fun_add (M N : V0) : b0Fun (M + N) = b0Fun M + b0Fun N := by
  ext i j <;> simp [b0Fun, frobFun, Matrix.transpose_apply, map_add]

theorem b0Fun_smul (c : ZMod 2) (M : V0) : b0Fun (c • M) = c • b0Fun M := by
  ext i j <;> simp [b0Fun, frobFun, Matrix.transpose_apply, frob_smul]

theorem b0Fun_b0Fun (M : V0) : b0Fun (b0Fun M) = M := by
  ext i j <;> simp [b0Fun, frobFun, Matrix.transpose_apply, frob_frob]

def b0 : V0 ≃ₗ[ZMod 2] V0 where
  toFun := b0Fun
  invFun := b0Fun
  map_add' := b0Fun_add
  map_smul' c M := b0Fun_smul c M
  left_inv := b0Fun_b0Fun
  right_inv := b0Fun_b0Fun

theorem omega_cube : F4.omega * (F4.omega * F4.omega) = 1 := by decide

theorem omegaFun_add (M N : V0) : omegaFun (M + N) = omegaFun M + omegaFun N := by
  simp [omegaFun]

theorem omegaFun_smul (c : ZMod 2) (M : V0) : omegaFun (c • M) = c • omegaFun M := by
  exact smul_comm F4.omega c M

theorem omegaFun_omegaFun_omegaFun (M : V0) : omegaFun (omegaFun (omegaFun M)) = M := by
  simp only [omegaFun, smul_smul, omega_cube, one_smul]

def omega0 : V0 ≃ₗ[ZMod 2] V0 where
  toFun := omegaFun
  invFun := omegaFun ∘ omegaFun
  map_add' := omegaFun_add
  map_smul' c M := omegaFun_smul c M
  left_inv M := omegaFun_omegaFun_omegaFun M
  right_inv M := omegaFun_omegaFun_omegaFun M

theorem q0_polar (M N : V0) : QuadraticMap.polar q0 M N = q0Polar M N := by
  simp only [QuadraticMap.polar, q0_apply, q0Fun_add]
  abel

theorem q0_nondegenerate : q0.polarBilin.Nondegenerate := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Module.Finite (ZMod 2) V0 := Module.Finite.of_finite
  refine LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft fun M hM => ?_
  refine q0Polar_nondeg M fun N => ?_
  have h := hM N
  rwa [QuadraticMap.polarBilin_apply_apply, q0_polar] at h

end CFSG.EvenSporadicStandard.HNRecog.CSide
