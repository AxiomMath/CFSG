module

public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

section Polar

variable (Q : QuadraticForm K V)

theorem polar_self_eq_two_mul (x : V) : polar Q x x = 2 * Q x := by
  rw [polar_self, nsmul_eq_mul, Nat.cast_ofNat]

variable {Q} in
theorem polar_self_eq_zero {x : V} (hx : Q x = 0) : polar Q x x = 0 := by
  rw [polar_self_eq_two_mul, hx, mul_zero]

theorem map_smul_eq_sq (c : K) (x : V) : Q (c • x) = c ^ 2 * Q x := by
  rw [QuadraticMap.map_smul, smul_eq_mul, pow_two]

theorem polar_smul_left_eq (c : K) (x y : V) : polar Q (c • x) y = c * polar Q x y := by
  rw [polar_smul_left, smul_eq_mul]

theorem polar_smul_right_eq (c : K) (x y : V) : polar Q x (c • y) = c * polar Q x y := by
  rw [polar_smul_right, smul_eq_mul]

variable {Q} in
theorem polar_map_of_mem {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (x y : V) : polar Q (g x) (g y) = polar Q x y :=
  TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg x y

variable {Q} in
theorem map_of_mem {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (x : V) :
    Q (g x) = Q x :=
  TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg x

variable {Q} in
theorem exists_polar_ne_zero (hQ : (polarBilin Q).Nondegenerate) {x : V} (hx : x ≠ 0) :
    ∃ y, polar Q x y ≠ 0 := by
  by_contra! h
  exact hx (hQ.1 x fun y => by simpa using h y)

variable {Q} in
theorem eq_zero_of_polar_eq_zero (hQ : (polarBilin Q).Nondegenerate) {x : V}
    (hx : ∀ y, polar Q x y = 0) : x = 0 :=
  hQ.1 x fun y => by simpa using hx y

end Polar

section Group

theorem LinearEquiv.apply_inv_apply' (g : V ≃ₗ[K] V) (v : V) : g (g⁻¹ v) = v := by
  rw [← LinearEquiv.mul_apply, mul_inv_cancel]
  rfl

theorem LinearEquiv.inv_apply_apply' (g : V ≃ₗ[K] V) (v : V) : g⁻¹ (g v) = v := by
  rw [← LinearEquiv.mul_apply, inv_mul_cancel]
  rfl

theorem ext_apply {g h : V ≃ₗ[K] V} (H : ∀ v, g v = h v) : g = h :=
  LinearEquiv.ext H

end Group

section Scalars

variable (K V)

def scalars : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | ∃ c : K, ∀ v, g v = c • v}
  one_mem' := ⟨1, fun v => by simp⟩
  mul_mem' := by
    rintro g h ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨d * c, fun v => by rw [LinearEquiv.mul_apply, hd, map_smul, hc, smul_smul]⟩
  inv_mem' := by
    rintro g ⟨c, hc⟩
    refine ⟨c⁻¹, fun v => ?_⟩
    by_cases h : c = 0
    · have hv : v = 0 := by
        have := hc (g⁻¹ v)
        rwa [LinearEquiv.apply_inv_apply', h, zero_smul] at this
      simp [hv]
    · apply g.injective
      rw [LinearEquiv.apply_inv_apply', map_smul, hc, smul_smul, inv_mul_cancel₀ h, one_smul]

variable {K V}

theorem mem_scalars {g : V ≃ₗ[K] V} : g ∈ scalars K V ↔ ∃ c : K, ∀ v, g v = c • v :=
  Iff.rfl

theorem commute_of_mem_scalars {g : V ≃ₗ[K] V} (hg : g ∈ scalars K V) (h : V ≃ₗ[K] V) :
    g * h = h * g := by
  obtain ⟨c, hc⟩ := hg
  exact LinearEquiv.ext fun v => by rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hc, hc,
    map_smul]

instance scalars_normal : (scalars K V).Normal where
  conj_mem g hg h := by
    rw [← commute_of_mem_scalars hg h, mul_inv_cancel_right]
    exact hg

end Scalars

section HypPair

structure HypPair (Q : QuadraticForm K V) where
  e : V
  f : V
  Q_e : Q e = 0
  Q_f : Q f = 0
  polar_ef : polar Q e f = 1

structure HypPair.Orth {Q : QuadraticForm K V} (P P' : HypPair Q) : Prop where
  ee : polar Q P.e P'.e = 0
  ef : polar Q P.e P'.f = 0
  fe : polar Q P.f P'.e = 0
  ff : polar Q P.f P'.f = 0

variable {Q : QuadraticForm K V}

namespace HypPair

theorem polar_fe (P : HypPair Q) : polar Q P.f P.e = 1 := by
  rw [polar_comm, P.polar_ef]

theorem polar_ee (P : HypPair Q) : polar Q P.e P.e = 0 := polar_self_eq_zero P.Q_e

theorem polar_ff (P : HypPair Q) : polar Q P.f P.f = 0 := polar_self_eq_zero P.Q_f

theorem e_ne_zero (P : HypPair Q) : P.e ≠ 0 := by
  intro h
  have := P.polar_ef
  rw [h, polar_zero_left] at this
  exact zero_ne_one this

theorem f_ne_zero (P : HypPair Q) : P.f ≠ 0 := by
  intro h
  have := P.polar_ef
  rw [h, polar_zero_right] at this
  exact zero_ne_one this

def swap (P : HypPair Q) : HypPair Q where
  e := P.f
  f := P.e
  Q_e := P.Q_f
  Q_f := P.Q_e
  polar_ef := P.polar_fe

def map (P : HypPair Q) {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    HypPair Q where
  e := g P.e
  f := g P.f
  Q_e := by rw [map_of_mem hg, P.Q_e]
  Q_f := by rw [map_of_mem hg, P.Q_f]
  polar_ef := by rw [polar_map_of_mem hg, P.polar_ef]

theorem Orth.symm {P P' : HypPair Q} (h : P.Orth P') : P'.Orth P where
  ee := by rw [polar_comm, h.ee]
  ef := by rw [polar_comm, h.fe]
  fe := by rw [polar_comm, h.ef]
  ff := by rw [polar_comm, h.ff]

end HypPair

end HypPair

end CFSG.ClassicalGroups.Orthogonal
