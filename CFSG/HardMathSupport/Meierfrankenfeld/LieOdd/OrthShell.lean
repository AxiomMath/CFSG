module

public import CFSG.ClassicalGroups.Orthogonal.Basic
public import Mathlib.FieldTheory.Finiteness

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

theorem quad_add_eq_add_polar {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (x y : V) : Q (x + y) = Q x + Q y + polar Q x y := by
  unfold polar
  ring

theorem polar_comb_e {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (P : HypPair Q) (α b : K) (v : V) (hv1 : polar Q v P.e = 0) :
    polar Q (α • P.e + b • P.f + v) P.e = b := by
  rw [polar_add_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq, P.polar_ee,
    P.polar_fe, hv1]
  ring

theorem polar_comb_f {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (P : HypPair Q) (α b : K) (v : V) (hv2 : polar Q v P.f = 0) :
    polar Q (α • P.e + b • P.f + v) P.f = α := by
  rw [polar_add_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq, P.polar_ef,
    P.polar_ff, hv2]
  ring

theorem quad_comb {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (P : HypPair Q) (α b : K) (v : V)
    (hv1 : polar Q v P.e = 0) (hv2 : polar Q v P.f = 0) :
    Q (α • P.e + b • P.f + v) = α * b + Q v := by
  have hX : polar Q (α • P.e + b • P.f) v = 0 := by
    rw [polar_comm, polar_add_right, polar_smul_right_eq, polar_smul_right_eq, hv1, hv2]
    ring
  rw [quad_add_eq_add_polar Q (α • P.e + b • P.f) v, hX, quad_add_eq_add_polar Q (α • P.e) (b • P.f),
    map_smul_eq_sq, map_smul_eq_sq, P.Q_e, P.Q_f, polar_smul_left_eq, polar_smul_right_eq,
    P.polar_ef]
  ring

theorem card_shell_ge {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V}
    (P : CFSG.ClassicalGroups.Orthogonal.HypPair Q) (c : K) :
    (Nat.card K - 1) * Nat.card K ^ (Module.finrank K V - 2) ≤
      Nat.card {v : V // v ≠ 0 ∧ Q v = c} := by
  classical
  have : Finite V := Module.finite_of_finite K
  let φ : V →ₗ[K] K × K :=
    ((polarBilin Q).flip P.e).prod ((polarBilin Q).flip P.f)
  have hφ : ∀ v, φ v = (polar Q v P.e, polar Q v P.f) := fun v => by
    simp [φ, polarBilin_apply_apply]
  have hker : ∀ v, v ∈ LinearMap.ker φ ↔ polar Q v P.e = 0 ∧ polar Q v P.f = 0 := fun v => by
    rw [LinearMap.mem_ker, hφ, Prod.mk_eq_zero]
  have hsurj : Function.Surjective φ := by
    rintro ⟨a, b⟩
    refine ⟨a • P.f + b • P.e, ?_⟩
    rw [hφ]
    refine Prod.ext ?_ ?_
    · show polar Q (a • P.f + b • P.e) P.e = a
      rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, P.polar_fe, P.polar_ee]
      ring
    · show polar Q (a • P.f + b • P.e) P.f = b
      rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, P.polar_ff, P.polar_ef]
      ring
  have hrank := LinearMap.finrank_range_add_finrank_ker φ
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_prod,
    Module.finrank_self] at hrank
  have hdim : Module.finrank K (LinearMap.ker φ) = Module.finrank K V - 2 := by omega
  obtain ⟨wv, hwv⟩ : ∃ wv : {b : K // b ≠ 0} × LinearMap.ker φ → V,
      ∀ x, wv x = ((c - Q x.2.1) * (x.1.1)⁻¹) • P.e + x.1.1 • P.f + x.2.1 :=
    ⟨_, fun x => rfl⟩
  have hmem : ∀ x, wv x ≠ 0 ∧ Q (wv x) = c := by
    intro x
    obtain ⟨hv1, hv2⟩ := (hker _).1 x.2.2
    have hb : x.1.1 ≠ 0 := x.1.2
    rw [hwv x]
    constructor
    · intro h
      have h1 := polar_comb_e P ((c - Q x.2.1) * (x.1.1)⁻¹) x.1.1 x.2.1 hv1
      rw [h, polar_zero_left] at h1
      exact hb h1.symm
    · rw [quad_comb P _ _ _ hv1 hv2, mul_assoc, inv_mul_cancel₀ hb, mul_one]
      ring
  have hcoordE : ∀ x, polar Q (wv x) P.e = x.1.1 := by
    intro x
    obtain ⟨hv1, -⟩ := (hker _).1 x.2.2
    rw [hwv x]
    exact polar_comb_e P _ _ _ hv1
  have key : ∀ x, x.2.1 = wv x - (polar Q (wv x) P.f • P.e + polar Q (wv x) P.e • P.f) := by
    intro x
    obtain ⟨hv1, hv2⟩ := (hker _).1 x.2.2
    rw [hwv x, polar_comb_e P _ _ _ hv1, polar_comb_f P _ _ _ hv2]
    abel
  have hinj : Function.Injective
      (fun x : {b : K // b ≠ 0} × LinearMap.ker φ => (⟨wv x, hmem x⟩ : {v : V // v ≠ 0 ∧ Q v = c})) := by
    intro x y hxy
    have hw : wv x = wv y := congrArg Subtype.val hxy
    have hb : x.1.1 = y.1.1 := by
      rw [← hcoordE x, ← hcoordE y, hw]
    have hv : x.2.1 = y.2.1 := by
      rw [key x, key y, hw]
    exact Prod.ext (Subtype.ext hb) (Subtype.ext hv)
  have hnz : Nat.card {b : K // b ≠ 0} + 1 = Nat.card K := by
    have : Fintype K := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      Fintype.card_subtype_eq]
    have : 0 < Fintype.card K := Fintype.card_pos
    omega
  have hnzK : Nat.card {b : K // b ≠ 0} = Nat.card K - 1 := by omega
  have hV1 : Nat.card (LinearMap.ker φ) = Nat.card K ^ (Module.finrank K V - 2) := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := LinearMap.ker φ), hdim]
  have hcard : Nat.card ({b : K // b ≠ 0} × LinearMap.ker φ) ≤
      Nat.card {v : V // v ≠ 0 ∧ Q v = c} :=
    Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod, hV1, hnzK] at hcard
  exact hcard

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

end
