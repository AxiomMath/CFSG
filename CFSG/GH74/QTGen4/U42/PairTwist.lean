module

public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

public section

namespace CFSG.GH74.QTGen4.U42.PairTwist

variable {K L : Type*} [Group K] [Group L]

def centralDiscrepancy (B : Subgroup K) (e : K ≃* L) (β : B →* L)
    (Z : Subgroup L) (hZ : Z ≤ Subgroup.center L)
    (hmod : ∀ b : B, (e (b : K))⁻¹ * β b ∈ Z) : B →* Z where
  toFun b := ⟨(e (b : K))⁻¹ * β b, hmod b⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' b c := by
    apply Subtype.ext
    change (e ((b * c : B) : K))⁻¹ * β (b * c) =
      ((e (b : K))⁻¹ * β b) * ((e (c : K))⁻¹ * β c)
    have hc : (e (c : K))⁻¹ * ((e (b : K))⁻¹ * β b) =
        ((e (b : K))⁻¹ * β b) * (e (c : K))⁻¹ :=
      Subgroup.mem_center_iff.mp (hZ (hmod b)) _
    simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]
    calc
      (e (c : K))⁻¹ * (e (b : K))⁻¹ * (β b * β c) =
          ((e (c : K))⁻¹ * ((e (b : K))⁻¹ * β b)) * β c := by
        simp only [mul_assoc]
      _ = (((e (b : K))⁻¹ * β b) * (e (c : K))⁻¹) * β c := by rw [hc]
      _ = ((e (b : K))⁻¹ * β b) * ((e (c : K))⁻¹ * β c) := by
        rw [mul_assoc]

theorem mul_centralDiscrepancy (B : Subgroup K) (e : K ≃* L) (β : B →* L)
    (Z : Subgroup L) (hZ : Z ≤ Subgroup.center L)
    (hmod : ∀ b : B, (e (b : K))⁻¹ * β b ∈ Z) (b : B) :
    e (b : K) * (centralDiscrepancy B e β Z hZ hmod b : L) = β b := by
  change e (b : K) * ((e (b : K))⁻¹ * β b) = β b
  exact mul_inv_cancel_left _ _

def centralShear (c : K →* K) (hcentral : ∀ x : K, c x ∈ Subgroup.center K)
    (hkill : ∀ x : K, c (c x) = 1) : K ≃* K where
  toFun x := c x * x
  invFun x := (c x)⁻¹ * x
  left_inv x := by
    simp only [map_mul, hkill, one_mul, mul_inv_rev]
    simp
  right_inv x := by
    simp only [map_mul, map_inv, hkill, inv_one, one_mul]
    simp
  map_mul' x y := by
    have hc : x * c y = c y * x := Subgroup.mem_center_iff.mp (hcentral y) x
    simp only [map_mul]
    calc
      (c x * c y) * (x * y) = c x * ((c y * x) * y) := by
        simp only [mul_assoc]
      _ = c x * ((x * c y) * y) := by rw [hc]
      _ = (c x * x) * (c y * y) := by simp only [mul_assoc]

theorem symm_mem_center (e : K ≃* L) {y : L} (hy : y ∈ Subgroup.center L) :
    e.symm y ∈ Subgroup.center K := by
  rw [Subgroup.mem_center_iff]
  intro x
  apply e.injective
  simpa only [map_mul, e.apply_symm_apply] using Subgroup.mem_center_iff.mp hy (e x)

def twist (e : K ≃* L) (Z : Subgroup L) (hZ : Z ≤ Subgroup.center L)
    (χ : K →* Z) (hkill : ∀ x : K, e x ∈ Z → χ x = 1) : K ≃* L :=
  let c : K →* K := e.symm.toMonoidHom.comp (Z.subtype.comp χ)
  have hc : ∀ x : K, c x ∈ Subgroup.center K := fun x =>
    symm_mem_center e (hZ (χ x).property)
  have hcc : ∀ x : K, c (c x) = 1 := by
    intro x
    have hx : e (c x) ∈ Z := by
      change e (e.symm (χ x : L)) ∈ Z
      rw [e.apply_symm_apply]
      exact (χ x).property
    change e.symm (χ (c x) : L) = 1
    have h := congrArg (fun a : Z => e.symm (a : L)) (hkill (c x) hx)
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype,
      Subgroup.coe_one, map_one] using h
  (centralShear c hc hcc).trans e

theorem twist_apply (e : K ≃* L) (Z : Subgroup L) (hZ : Z ≤ Subgroup.center L)
    (χ : K →* Z) (hkill : ∀ x : K, e x ∈ Z → χ x = 1) (x : K) :
    twist e Z hZ χ hkill x = e x * (χ x : L) := by
  change e (e.symm (χ x : L) * x) = e x * (χ x : L)
  rw [map_mul, e.apply_symm_apply]
  exact (Subgroup.mem_center_iff.mp (hZ (χ x).property) (e x)).symm

theorem twist_eq_on (B : Subgroup K) (e : K ≃* L) (β : B →* L)
    (Z : Subgroup L) (hZ : Z ≤ Subgroup.center L)
    (hmod : ∀ b : B, (e (b : K))⁻¹ * β b ∈ Z)
    (χ : K →* Z) (hkill : ∀ x : K, e x ∈ Z → χ x = 1)
    (hext : ∀ b : B, χ (b : K) = centralDiscrepancy B e β Z hZ hmod b) (b : B) :
    twist e Z hZ χ hkill (b : K) = β b := by
  rw [twist_apply, hext]
  exact mul_centralDiscrepancy B e β Z hZ hmod b

theorem hom_eq_one_of_mem_zpowers {A : Type*} [Group A] (χ : K →* A)
    (z : K) (hz : χ z = 1) (x : K) (hx : x ∈ Subgroup.zpowers z) : χ x = 1 := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [map_zpow, hz, one_zpow]

theorem kills_central_preimage (e : K ≃* L) (Z : Subgroup L) (χ : K →* Z)
    (z : K) (hz : χ z = 1) (hpre : ∀ x : K, e x ∈ Z → x ∈ Subgroup.zpowers z) :
    ∀ x : K, e x ∈ Z → χ x = 1 := by
  intro x hx
  exact hom_eq_one_of_mem_zpowers χ z hz x (hpre x hx)

end CFSG.GH74.QTGen4.U42.PairTwist
