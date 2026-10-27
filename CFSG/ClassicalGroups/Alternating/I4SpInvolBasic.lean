module

public import CFSG.ClassicalGroups.Alternating.RT1SpBasic

public section

namespace CFSG.ClassicalGroups.Alternating

open LinearMap (BilinForm)

variable {K N : Type*} [Field K] [AddCommGroup N] [Module K N] {BN : BilinForm K N}

@[expose] def Gsp.phi (t : Gsp BN) : N →ₗ[K] N :=
  ((t : LinearMap.GeneralLinearGroup K N) : N →ₗ[K] N) - 1

@[expose] def Gsp.ft (t : Gsp BN) (v : N) : K := BN v (t.app v)

theorem Gsp.map_sub (g : Gsp BN) (v w : N) : g.app (v - w) = g.app v - g.app w :=
  _root_.map_sub ((g : LinearMap.GeneralLinearGroup K N) : N →ₗ[K] N) v w

theorem Gsp.phi_apply (t : Gsp BN) (x : N) : t.phi x = t.app x - x := rfl

theorem Gsp.app_app_of_mul_self {t : Gsp BN} (ht : t * t = 1) (x : N) : t.app (t.app x) = x := by
  have h := congrArg (fun g : Gsp BN => g.app x) ht
  simpa only [Gsp.app_mul, Gsp.app_one] using h

theorem Gsp.phi_phi [CharP K 2] {t : Gsp BN} (ht : t * t = 1) (x : N) :
    t.phi (t.phi x) = 0 := by
  rw [Gsp.phi_apply, Gsp.phi_apply, Gsp.map_sub, Gsp.app_app_of_mul_self ht]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have : x - t.app x - (t.app x - x) = (2 : K) • (x - t.app x) := by module
  rw [this, h2, zero_smul]

theorem Gsp.form_phi_left {t : Gsp BN} (ht : t * t = 1) (x y : N) :
    BN (t.phi x) y = BN x (t.phi y) := by
  have h : BN (t.app x) y = BN x (t.app y) := by
    have h1 := Gsp.form_app t x (t.app y)
    rw [Gsp.app_app_of_mul_self ht] at h1
    exact h1
  rw [Gsp.phi_apply, Gsp.phi_apply, _root_.map_sub, _root_.map_sub, LinearMap.sub_apply, h]

theorem Gsp.form_phi_phi [CharP K 2] {t : Gsp BN} (ht : t * t = 1) (x y : N) :
    BN (t.phi x) (t.phi y) = 0 := by
  rw [Gsp.form_phi_left ht, Gsp.phi_phi ht, _root_.map_zero]

theorem Gsp.ft_eq_form_phi (hBN : BN.IsAlt) (t : Gsp BN) (v : N) : t.ft v = BN v (t.phi v) := by
  rw [Gsp.ft, Gsp.phi_apply, _root_.map_sub, hBN.self_eq_zero, sub_zero]

theorem Gsp.ft_add (hBN : BN.IsAlt) {t : Gsp BN} (ht : t * t = 1) (v w : N) :
    t.ft (v + w) = t.ft v + t.ft w := by
  have hcross : BN w (t.app v) = - BN v (t.app w) := by
    have h1 := Gsp.form_app t w (t.app v)
    rw [Gsp.app_app_of_mul_self ht] at h1
    rw [← h1]
    exact (hBN.neg_eq v (t.app w)).symm
  simp only [Gsp.ft, Gsp.map_add, _root_.map_add, LinearMap.add_apply, hcross]
  ring

theorem Gsp.ft_smul (t : Gsp BN) (c : K) (v : N) : t.ft (c • v) = c ^ 2 * t.ft v := by
  simp only [Gsp.ft, Gsp.map_smul, _root_.map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

@[expose] def Gsp.fixator (S : Set N) : Subgroup (Gsp BN) where
  carrier := {g | ∀ x ∈ S, g.app x = x}
  one_mem' := fun x _ => Gsp.app_one x
  mul_mem' := fun {g h} hg hh x hx => by rw [Gsp.app_mul, hh x hx, hg x hx]
  inv_mem' := fun {g} hg x hx => by
    conv_lhs => rw [← hg x hx]
    exact Gsp.app_inv_app g x

theorem commute_Tsp_of_app_eq (hBN : BN.IsAlt) {g : Gsp BN} {a : N} (c : K)
    (ha : g.app a = a) : Commute g (Tsp hBN a c) := by
  have h := Tsp_conj hBN g a c
  rw [ha] at h
  exact mul_inv_eq_iff_eq_mul.mp h

theorem Tsp_app_of_form_eq_zero (hBN : BN.IsAlt) {a x : N} (c : K) (h : BN x a = 0) :
    (Tsp hBN a c).app x = x := by
  rw [Tsp_app, h, mul_zero, zero_smul, add_zero]

end CFSG.ClassicalGroups.Alternating
