module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

open Module

theorem pow_three_eq_zero_of_two_le_finrank_ker {K W : Type*} [Field K] [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] (hW : finrank K W = 4) {f : Module.End K W}
    (h5 : f ^ 5 = 0) (hk : 2 ≤ finrank K (LinearMap.ker f)) : f ^ 3 = 0 := by
  by_contra h3
  have hle : ∀ j : ℕ, LinearMap.ker (f ^ j) ≤ LinearMap.ker (f ^ (j + 1)) := fun j => by
    rw [pow_succ']
    exact LinearMap.ker_le_ker_comp (f ^ j) f
  have hne : ∀ j : ℕ, j ≤ 3 → LinearMap.ker (f ^ j) < LinearMap.ker (f ^ (j + 1)) := by
    intro j hj
    refine lt_of_le_of_ne (hle j) fun heq => h3 ?_
    have h := Module.End.ker_pow_constant (f := f) (k := j) heq 5
    have hz : f ^ (j + 5) = 0 := by rw [pow_add, h5, mul_zero]
    rw [hz, LinearMap.ker_zero] at h
    have hj0 : f ^ j = 0 := LinearMap.ker_eq_top.mp h
    have e3 : f ^ 3 = f ^ (3 - j) * f ^ j := by
      rw [← pow_add]
      congr 1
      omega
    rw [e3, hj0, mul_zero]
  have d1 : 2 ≤ finrank K (LinearMap.ker (f ^ 1)) := by rw [pow_one]; exact hk
  have d2 : finrank K (LinearMap.ker (f ^ 1)) < finrank K (LinearMap.ker (f ^ 2)) :=
    Submodule.finrank_lt_finrank_of_lt (hne 1 (by norm_num))
  have d3 : finrank K (LinearMap.ker (f ^ 2)) < finrank K (LinearMap.ker (f ^ 3)) :=
    Submodule.finrank_lt_finrank_of_lt (hne 2 (by norm_num))
  have d4 := Submodule.finrank_le (LinearMap.ker (f ^ 3))
  have htop : LinearMap.ker (f ^ 3) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by omega)
  exact h3 (LinearMap.ker_eq_top.mp htop)

theorem pow_three_apply_eq_zero {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {N : Module.End K V} (h5 : N ^ 5 = 0) {E : Submodule K V} (hE : ∀ x ∈ E, N x ∈ E)
    [FiniteDimensional K E] (hd : finrank K E = 4)
    (hk : 2 ≤ finrank K ↥(E ⊓ LinearMap.ker N)) : ∀ x ∈ E, (N ^ 3) x = 0 := by
  have hf5 : N.restrict hE ^ 5 = 0 := by
    rw [Module.End.pow_restrict 5 hE]
    ext x
    have hx5 : (N ^ 5) (x : V) = 0 := by rw [h5]; rfl
    simpa using hx5
  have hker : finrank K (LinearMap.ker (N.restrict hE)) = finrank K ↥(E ⊓ LinearMap.ker N) := by
    rw [LinearMap.ker_restrict, ← Submodule.finrank_map_subtype_eq E, Submodule.map_comap_subtype]
  have h3 := pow_three_eq_zero_of_two_le_finrank_ker hd hf5 (hker ▸ hk)
  intro x hx
  have h4 : ((N.restrict hE ^ 3) ⟨x, hx⟩ : E) = 0 := by rw [h3]; rfl
  rw [Module.End.pow_restrict 3 hE] at h4
  simpa using congrArg Subtype.val h4

theorem sub_one_pow_apply {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (n : ℕ) (x : V) : ((T - 1) ^ n) x = (fun y => T y - y)^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih, Function.iterate_succ_apply]
    rfl

end CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

end
