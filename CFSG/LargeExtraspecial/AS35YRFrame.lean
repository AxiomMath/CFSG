module

public import CFSG.ClassicalGroups.Orthogonal.Eichler
public import CFSG.RankThree.OrthogonalInvolutions.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.ClassicalGroups.Orthogonal

namespace AS35YR

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}

theorem add_self_YR (v : V) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem neg_YR (v : V) : -v = v := by
  rw [neg_eq_iff_add_eq_zero, add_self_YR]

theorem sub_YR (u v : V) : u - v = u + v := by
  rw [sub_eq_add_neg, neg_YR]

theorem siegel_apply {u w : V} (hu : q u = 0) (hw : q w = 0) (huw : polar q u w = 0) (x : V) :
    eichler q u w x = x + polar q x u • w + polar q x w • u := by
  rw [eichler_apply hu huw, hw, zero_mul, add_zero, sub_YR]

theorem siegel_mul_self {u w : V} (huw : polar q u w = 0) :
    eichler q u w * eichler q u w = 1 := by
  rw [eichler_mul huw huw, add_self_YR, eichler_zero_right]

structure Frame (q : QuadraticForm (ZMod 2) V) where
  a : V
  b : V
  c : V
  c' : V
  qa : q a = 0
  qb : q b = 0
  qc : q c = 0
  qc' : q c' = 0
  ab : polar q a b = 0
  ac : polar q a c = 0
  bc : polar q b c = 1
  ac' : polar q a c' = 1
  bc' : polar q b c' = 0
  cc' : polar q c c' = 0

namespace Frame

variable (F : Frame q)

abbrev ell : Submodule (ZMod 2) V := Submodule.span (ZMod 2) {F.a, F.b}

noncomputable abbrev t : V ≃ₗ[ZMod 2] V := eichler q F.a F.b

@[expose] noncomputable def proj : V →ₗ[ZMod 2] V :=
  LinearMap.id - (LinearMap.smulRight ((polarBilin q).flip F.c') F.a +
    LinearMap.smulRight ((polarBilin q).flip F.c) F.b)

theorem proj_apply (u : V) : F.proj u = u - (polar q u F.c' • F.a + polar q u F.c • F.b) := by
  simp [proj, polarBilin_apply_apply]

theorem polar_proj_c (u : V) : polar q (F.proj u) F.c = 0 := by
  rw [proj_apply, polar_sub_left, polar_add_left, polar_smul_left, polar_smul_left, F.ac, F.bc]
  simp

theorem polar_proj_c' (u : V) : polar q (F.proj u) F.c' = 0 := by
  rw [proj_apply, polar_sub_left, polar_add_left, polar_smul_left, polar_smul_left, F.ac',
    F.bc']
  simp

theorem polar_proj_a (u : V) : polar q (F.proj u) F.a = polar q u F.a := by
  rw [proj_apply, polar_sub_left, polar_add_left, polar_smul_left, polar_smul_left,
    polar_self_eq_zero F.qa, polar_comm q F.b F.a, F.ab]
  simp

theorem polar_proj_b (u : V) : polar q (F.proj u) F.b = polar q u F.b := by
  rw [proj_apply, polar_sub_left, polar_add_left, polar_smul_left, polar_smul_left,
    polar_self_eq_zero F.qb, F.ab]
  simp

theorem proj_a : F.proj F.a = 0 := by
  rw [proj_apply, F.ac', F.ac]
  simp

theorem proj_b : F.proj F.b = 0 := by
  rw [proj_apply, F.bc', F.bc]
  simp

theorem proj_eq_zero_of_mem_ell {u : V} (hu : u ∈ F.ell) : F.proj u = 0 := by
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hu
  rw [map_add, map_smul, map_smul, F.proj_a, F.proj_b, smul_zero, smul_zero, add_zero]

theorem eq_of_mem_ell {z : V} (hz : z ∈ F.ell) :
    z = polar q z F.c' • F.a + polar q z F.c • F.b := by
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hz
  rw [polar_add_left, polar_add_left, polar_smul_left, polar_smul_left, polar_smul_left,
    polar_smul_left, F.ac', F.bc', F.bc, F.ac]
  simp

theorem eq_zero_of_mem_ell {z : V} (hz : z ∈ F.ell) (hc : polar q z F.c = 0)
    (hc' : polar q z F.c' = 0) : z = 0 := by
  rw [F.eq_of_mem_ell hz, hc, hc', zero_smul, zero_smul, add_zero]

theorem sub_proj_mem_ell (u : V) : u - F.proj u ∈ F.ell := by
  rw [proj_apply, sub_sub_cancel]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

theorem polar_decomp_a (u : V) :
    polar q (u - (polar q u F.a • F.c' + polar q u F.b • F.c)) F.a = 0 := by
  rw [polar_sub_left, polar_add_left, polar_smul_left, polar_smul_left, polar_comm q F.c' F.a,
    F.ac', polar_comm q F.c F.a, F.ac]
  simp

theorem polar_decomp_b (u : V) :
    polar q (u - (polar q u F.a • F.c' + polar q u F.b • F.c)) F.b = 0 := by
  rw [polar_sub_left, polar_add_left, polar_smul_left, polar_smul_left, polar_comm q F.c' F.b,
    F.bc', polar_comm q F.c F.b, F.bc]
  simp

theorem linearMap_ext {φ ψ : V →ₗ[ZMod 2] V}
    (hperp : ∀ u, polar q u F.a = 0 → polar q u F.b = 0 → φ u = ψ u) (hc : φ F.c = ψ F.c)
    (hc' : φ F.c' = ψ F.c') : φ = ψ := by
  ext v
  have e : v = (v - (polar q v F.a • F.c' + polar q v F.b • F.c)) +
      (polar q v F.a • F.c' + polar q v F.b • F.c) := by abel
  rw [e, map_add, map_add, hperp _ (F.polar_decomp_a v) (F.polar_decomp_b v), map_add, map_add,
    map_smul, map_smul, map_smul, map_smul, hc, hc']

theorem t_apply (x : V) : F.t x = x + polar q x F.a • F.b + polar q x F.b • F.a :=
  siegel_apply F.qa F.qb F.ab x

theorem t_mul_self : F.t * F.t = 1 := siegel_mul_self F.ab

theorem t_mem : F.t ∈ TauCeti.QuadraticMap.orthogonalGroup q := eichler_mem_orthogonalGroup q _ _

structure InU (p : V ≃ₗ[ZMod 2] V) : Prop where
  mem : p ∈ TauCeti.QuadraticMap.orthogonalGroup q
  fix_a : p F.a = F.a
  fix_b : p F.b = F.b
  sub_mem : ∀ v, polar q v F.a = 0 → polar q v F.b = 0 → p v - v ∈ F.ell

variable {F}

theorem polar_ell_of_perp {z w : V} (hz : z ∈ F.ell) (ha : polar q w F.a = 0)
    (hb : polar q w F.b = 0) : polar q z w = 0 := by
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hz
  rw [polar_add_left, polar_smul_left, polar_smul_left, polar_comm q F.a w, polar_comm q F.b w,
    ha, hb]
  simp

namespace InU

variable {p : V ≃ₗ[ZMod 2] V} (hp : F.InU p)
include hp

theorem polar_sub_a (v : V) : polar q (p v - v) F.a = 0 := by
  have h := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hp.mem v F.a
  rw [hp.fix_a] at h
  rw [polar_sub_left, h, sub_self]

theorem polar_sub_b (v : V) : polar q (p v - v) F.b = 0 := by
  have h := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hp.mem v F.b
  rw [hp.fix_b] at h
  rw [polar_sub_left, h, sub_self]

theorem adjoint {u : V} (ha : polar q u F.a = 0) (hb : polar q u F.b = 0) (y : V) :
    polar q (p u - u) y = polar q u (p y - y) := by
  have hiso := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hp.mem u y
  have hN : polar q (p u - u) (p y - y) = 0 :=
    polar_ell_of_perp (hp.sub_mem u ha hb) (hp.polar_sub_a y) (hp.polar_sub_b y)
  have e1 : p u = u + (p u - u) := by abel
  have e2 : p y = y + (p y - y) := by abel
  rw [e1, e2, polar_add_left, polar_add_right, polar_add_right, hN, add_zero] at hiso
  have : polar q (p u - u) y = -polar q u (p y - y) := by
    linear_combination hiso
  rw [this]
  exact neg_eq_iff_add_eq_zero.mpr (CharTwo.add_self_eq_zero _)

end InU

@[expose] noncomputable def tau (F : Frame q) (p : V ≃ₗ[ZMod 2] V) (v : V) : V := F.proj (p v - v)

theorem tau_def (p : V ≃ₗ[ZMod 2] V) (v : V) : F.tau p v = F.proj (p v - v) := rfl

theorem tau_add (p : V ≃ₗ[ZMod 2] V) (v w : V) : F.tau p (v + w) = F.tau p v + F.tau p w := by
  rw [tau, tau, tau, ← map_add]
  congr 1
  rw [map_add]
  abel

theorem polar_tau_a {p : V ≃ₗ[ZMod 2] V} (hp : F.InU p) (v : V) :
    polar q (F.tau p v) F.a = 0 := by
  rw [tau, F.polar_proj_a, hp.polar_sub_a]

theorem polar_tau_b {p : V ≃ₗ[ZMod 2] V} (hp : F.InU p) (v : V) :
    polar q (F.tau p v) F.b = 0 := by
  rw [tau, F.polar_proj_b, hp.polar_sub_b]

theorem polar_tau_c (p : V ≃ₗ[ZMod 2] V) (v : V) : polar q (F.tau p v) F.c = 0 :=
  F.polar_proj_c _

theorem polar_tau_c' (p : V ≃ₗ[ZMod 2] V) (v : V) : polar q (F.tau p v) F.c' = 0 :=
  F.polar_proj_c' _

theorem tau_mul {p₁ p₂ : V ≃ₗ[ZMod 2] V} (h₁ : F.InU p₁) (h₂ : F.InU p₂) (v : V) :
    F.tau (p₁ * p₂) v = F.tau p₁ v + F.tau p₂ v := by
  have hw := h₁.sub_mem (p₂ v - v) (h₂.polar_sub_a v) (h₂.polar_sub_b v)
  have e : (p₁ * p₂) v - v = (p₁ v - v) + (p₂ v - v) + (p₁ (p₂ v - v) - (p₂ v - v)) := by
    rw [LinearEquiv.mul_apply, map_sub]
    abel
  rw [tau, e, map_add, map_add, F.proj_eq_zero_of_mem_ell hw, add_zero]
  rfl

end Frame

end AS35YR

end CFSG.LargeExtraspecial
