module

public import CFSG.ClassicalGroups.Orthogonal.Eichler

public section

namespace CFSG.SeitzReduction

namespace OrthogonalLagrangian

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

structure IsLagrangianDisplacement (Q : QuadraticForm K V) (N : V →ₗ[K] V) : Prop where
  sq : ∀ x, N (N x) = 0
  polar_left : ∀ x y, polar Q (N x) y = polar Q x (N y)
  diag : ∀ x, Q (N x) = polar Q x (N x)
  ker_le : ∀ x, N x = 0 → ∃ y, N y = x

variable (K) in
theorem vec_add_self_eq_zero [CharP K 2] (x : V) : x + x = 0 := by
  rw [← two_smul K x, CharTwo.two_eq_zero, zero_smul]

variable (K) in
theorem vec_sub_eq_add [CharP K 2] (x y : V) : x - y = x + y := by
  rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_left (vec_add_self_eq_zero K y)]

@[expose] noncomputable def leviEichler (Q : QuadraticForm K V) (N : V →ₗ[K] V) (u : V) :
    V ≃ₗ[K] V :=
  eichler Q (N u) u

@[expose] noncomputable def leviPair (Q : QuadraticForm K V) (N : V →ₗ[K] V) (u v : V) :
    V ≃ₗ[K] V :=
  (leviEichler Q N u * leviEichler Q N v) ^ 4

variable {Q : QuadraticForm K V} {N : V →ₗ[K] V}

namespace IsLagrangianDisplacement

variable (hL : IsLagrangianDisplacement Q N)
include hL

theorem polar_N_N (x y : V) : polar Q (N x) (N y) = 0 := by
  rw [hL.polar_left, hL.sq, polar_zero_right]

theorem polar_N_of_ker {k : V} (hk : N k = 0) (x : V) : polar Q (N x) k = 0 := by
  rw [hL.polar_left, hk, polar_zero_right]

theorem polar_of_ker_N {k : V} (hk : N k = 0) (x : V) : polar Q k (N x) = 0 := by
  rw [polar_comm, hL.polar_N_of_ker hk]

theorem polar_of_ker_of_ker {k k' : V} (hk : N k = 0) (hk' : N k' = 0) : polar Q k k' = 0 := by
  obtain ⟨y, rfl⟩ := hL.ker_le k hk
  exact hL.polar_N_of_ker hk' y

theorem polar_N_self (u : V) : polar Q (N u) u = Q (N u) := by
  rw [polar_comm, hL.diag]

theorem polar_self_N (u : V) : polar Q u (N u) = Q (N u) := (hL.diag u).symm

theorem polar_swap (u v : V) : polar Q v (N u) = polar Q u (N v) := by
  rw [← hL.polar_left, polar_comm]

theorem map_add_of_ker {k k' : V} (hk : N k = 0) (hk' : N k' = 0) :
    Q (k + k') = Q k + Q k' := by
  rw [QuadraticMap.map_add Q k k', hL.polar_of_ker_of_ker hk hk', add_zero]

theorem leviEichler_apply {u : V} (hu : Q (N u) = 0) (x : V) :
    leviEichler Q N u x = x + polar Q x (N u) • u - (polar Q x u + Q u * polar Q x (N u)) • N u :=
  eichler_apply hu (by rw [hL.polar_N_self, hu]) x

theorem leviEichler_apply_of_ker [CharP K 2] {u : V} (hu : Q (N u) = 0) {x : V} (hx : N x = 0) :
    leviEichler Q N u x = x + polar Q x u • N u := by
  rw [hL.leviEichler_apply hu, polar_comm Q x (N u), hL.polar_N_of_ker hx, zero_smul, add_zero,
    mul_zero,
    add_zero, vec_sub_eq_add K]

theorem leviEichler_apply_N [CharP K 2] {u : V} (hu : Q (N u) = 0) (x : V) :
    leviEichler Q N u (N x) = N (leviEichler Q N u x) := by
  rw [hL.leviEichler_apply_of_ker hu (hL.sq x), hL.leviEichler_apply hu, map_sub, map_add, map_smul,
    map_smul,
    hL.sq u, smul_zero, sub_zero, hL.polar_left]

theorem leviEichler_ker [CharP K 2] {u : V} (hu : Q (N u) = 0) {x : V} (hx : N x = 0) :
    N (leviEichler Q N u x) = 0 := by
  rw [hL.leviEichler_apply_of_ker hu hx, map_add, map_smul, hx, hL.sq, smul_zero, add_zero]

section Pair

variable [CharP K 2] {u v : V} (hu : Q (N u) = 0) (hv : Q (N v) = 0)
  (huv : polar Q u (N v) = 1)
include hu hv huv

theorem pair_apply_of_ker {x : V} (hx : N x = 0) :
    (leviEichler Q N u * leviEichler Q N v) x =
      x + polar Q x v • N v + (polar Q x u + polar Q x v) • N u := by
  rw [LinearEquiv.mul_apply, hL.leviEichler_apply_of_ker hv hx, hL.leviEichler_apply_of_ker hu
    (by rw [map_add, map_smul, hx, hL.sq, smul_zero, add_zero]), polar_add_left, polar_smul_left,
    polar_comm Q (N v) u, huv, smul_eq_mul, mul_one]

theorem pair_apply_step {x : V} (hx : N x = 0) (α β : K) :
    (leviEichler Q N u * leviEichler Q N v) (x + α • N v + β • N u) =
      x + (α + polar Q x v + β) • N v + (α + β + polar Q x u + polar Q x v + β) • N u := by
  have hk : N (x + α • N v + β • N u) = 0 := by
    rw [map_add, map_add, map_smul, map_smul, hx, hL.sq, hL.sq, smul_zero, smul_zero, add_zero,
      add_zero]
  have h1 : polar Q (N v) v = 0 := by rw [hL.polar_N_self, hv]
  have h2 : polar Q (N u) u = 0 := by rw [hL.polar_N_self, hu]
  have h3 : polar Q (N v) u = 1 := by rw [polar_comm, huv]
  have h4 : polar Q (N u) v = 1 := by rw [hL.polar_left, huv]
  rw [hL.pair_apply_of_ker hu hv huv hk]
  simp only [polar_add_left, polar_smul_left, h1, h2, h3, h4, smul_eq_mul, mul_zero, mul_one,
    add_zero]
  module

theorem pair_pow_three_apply_of_ker {x : V} (hx : N x = 0) :
    ((leviEichler Q N u * leviEichler Q N v) ^ 3) x = x := by
  set p := polar Q x u
  set q := polar Q x v
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  have s1 : (leviEichler Q N u * leviEichler Q N v) x = x + q • N v + (p + q) • N u :=
    hL.pair_apply_of_ker hu hv huv hx
  have s2 := hL.pair_apply_step hu hv huv hx q (p + q)
  have s3 := hL.pair_apply_step hu hv huv hx (q + q + (p + q))
    (q + (p + q) + p + q + (p + q))
  rw [pow_succ, pow_succ, pow_one, LinearEquiv.mul_apply, LinearEquiv.mul_apply, s1, s2, s3]
  have c1 : q + q + (p + q) + q + (q + (p + q) + p + q + (p + q)) = 0 := by
    linear_combination (2 * (p + 2 * q)) * h2K
  have c2 : q + q + (p + q) + (q + (p + q) + p + q + (p + q)) + p + q +
      (q + (p + q) + p + q + (p + q)) = 0 := by
    linear_combination (2 * (2 * p + 3 * q)) * h2K
  rw [c1, c2, zero_smul, zero_smul, add_zero, add_zero]

omit huv in
theorem pair_apply_N (x : V) :
    (leviEichler Q N u * leviEichler Q N v) (N x) =
      N ((leviEichler Q N u * leviEichler Q N v) x) := by
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hL.leviEichler_apply_N hv,
    hL.leviEichler_apply_N hu]

omit huv in
theorem pair_pow_apply_N (k : ℕ) (x : V) :
    ((leviEichler Q N u * leviEichler Q N v) ^ k) (N x) =
      N (((leviEichler Q N u * leviEichler Q N v) ^ k) x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, LinearEquiv.mul_apply, hL.pair_apply_N hu hv, ih]
    rfl

theorem pair_pow_six : (leviEichler Q N u * leviEichler Q N v) ^ 6 = 1 := by
  set h := leviEichler Q N u * leviEichler Q N v
  refine LinearEquiv.ext fun x => ?_
  have hk : N ((h ^ 3) x - x) = 0 := by
    rw [map_sub, ← hL.pair_pow_apply_N hu hv 3,
      hL.pair_pow_three_apply_of_ker hu hv huv (hL.sq x), sub_self]
  have h3 := hL.pair_pow_three_apply_of_ker hu hv huv hk
  rw [show (6 : ℕ) = 3 + 3 from rfl, pow_add, LinearEquiv.mul_apply]
  change (h ^ 3) ((h ^ 3) x) = x
  have e : (h ^ 3) x = x + ((h ^ 3) x - x) := by abel
  rw [e, map_add, h3, ← add_sub_assoc, vec_add_self_eq_zero K, zero_sub,
    neg_eq_of_add_eq_zero_left (vec_add_self_eq_zero K x)]

theorem leviPair_pow_three : leviPair Q N u v ^ 3 = 1 := by
  rw [leviPair, ← pow_mul, show 4 * 3 = 6 * 2 from rfl, pow_mul, hL.pair_pow_six hu hv huv,
    one_pow]

theorem leviPair_apply_of_ker {x : V} (hx : N x = 0) :
    leviPair Q N u v x = x + polar Q x v • N v + (polar Q x u + polar Q x v) • N u := by
  have hk : N ((leviEichler Q N u * leviEichler Q N v) x) = 0 := by
    rw [hL.pair_apply_of_ker hu hv huv hx, map_add, map_add, map_smul, map_smul, hx, hL.sq,
      hL.sq, smul_zero, smul_zero, add_zero, add_zero]
  rw [leviPair, pow_succ, LinearEquiv.mul_apply, hL.pair_pow_three_apply_of_ker hu hv huv hk,
    hL.pair_apply_of_ker hu hv huv hx]

omit huv in
theorem leviPair_apply_N (x : V) : leviPair Q N u v (N x) = N (leviPair Q N u v x) :=
  hL.pair_pow_apply_N hu hv 4 x

end Pair

theorem eichler_apply_N_of_ker [CharP K 2] {v w : V} (hv : Q (N v) = 0) (hw : N w = 0)
    (x : V) : eichler Q (N v) w (N x) = N x := by
  rw [eichler_apply hv (hL.polar_N_of_ker hw v), hL.polar_N_N, hL.polar_N_of_ker hw x,
    zero_smul, add_zero, mul_zero, add_zero, zero_smul, sub_zero]

theorem N_eichler_apply_of_ker [CharP K 2] {v w : V} (hv : Q (N v) = 0) (hw : N w = 0)
    (x : V) : N (eichler Q (N v) w x) = N x := by
  rw [eichler_apply hv (hL.polar_N_of_ker hw v), map_sub, map_add, map_smul, map_smul, hw,
    hL.sq, smul_zero, smul_zero, add_zero, sub_zero]

theorem eichler_apply_N [CharP K 2] {v w : V} (hv : Q (N v) = 0) (hw : N w = 0) (x : V) :
    eichler Q (N v) w (N x) = N (eichler Q (N v) w x) := by
  rw [hL.eichler_apply_N_of_ker hv hw, hL.N_eichler_apply_of_ker hv hw]

omit hL in
theorem inv_apply_N {g : V ≃ₗ[K] V} (hg : ∀ x, g (N x) = N (g x)) (x : V) :
    g⁻¹ (N x) = N (g⁻¹ x) := by
  apply g.injective
  rw [hg, LinearEquiv.apply_inv_apply', LinearEquiv.apply_inv_apply']

end IsLagrangianDisplacement

theorem leviEichler_mem_elementaryGroup (u : V) : leviEichler Q N u ∈ elementaryGroup Q :=
  eichler_mem_elementaryGroup Q _ _

theorem leviPair_mem_elementaryGroup (u v : V) : leviPair Q N u v ∈ elementaryGroup Q :=
  pow_mem (mul_mem (leviEichler_mem_elementaryGroup u) (leviEichler_mem_elementaryGroup v)) 4

end OrthogonalLagrangian

end CFSG.SeitzReduction
