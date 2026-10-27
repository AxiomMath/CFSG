module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.FixedSubmodule
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Data.ZMod.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open DirectSum Finset

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

section InternalProj

variable {ι : Type*} [DecidableEq ι] {W : ι → Submodule R V}

noncomputable def internalProj (hW : IsInternal W) (i : ι) : V →ₗ[R] W i :=
  (DirectSum.component R ι (fun i => (W i : Type _)) i).comp
    (LinearEquiv.ofBijective (coeLinearMap W) hW).symm.toLinearMap

theorem internalProj_apply (hW : IsInternal W) (i : ι) (x : V) :
    internalProj hW i x = (LinearEquiv.ofBijective (coeLinearMap W) hW).symm x i := (rfl)

@[simp]
theorem internalProj_of_mem (hW : IsInternal W) {i : ι} {x : V} (hx : x ∈ W i) :
    (internalProj hW i x : V) = x := by
  rw [internalProj_apply, hW.ofBijective_coeLinearMap_of_mem hx]

@[simp]
theorem internalProj_of_mem_ne (hW : IsInternal W) {i j : ι} (hij : i ≠ j) {x : V}
    (hx : x ∈ W i) : internalProj hW j x = 0 := by
  rw [internalProj_apply, hW.ofBijective_coeLinearMap_of_mem_ne hij hx]

variable [Fintype ι]

theorem sum_internalProj (hW : IsInternal W) (x : V) : ∑ i, (internalProj hW i x : V) = x := by
  set y := (LinearEquiv.ofBijective (coeLinearMap W) hW).symm x with hy
  have hx : coeLinearMap W y = x := (LinearEquiv.ofBijective (coeLinearMap W) hW).apply_symm_apply x
  calc ∑ i, (internalProj hW i x : V) = ∑ i, ((y i : V)) := by simp [internalProj_apply, hy]
    _ = coeLinearMap W y := by
        conv_rhs => rw [← DirectSum.sum_univ_of y]
        rw [map_sum]; simp
    _ = x := hx

theorem internalProj_sum_of_mem (hW : IsInternal W) {x : ι → V} (hx : ∀ i, x i ∈ W i) (j : ι) :
    (internalProj hW j (∑ i, x i) : V) = x j := by
  rw [map_sum]
  push_cast
  rw [Finset.sum_eq_single j]
  · exact internalProj_of_mem hW (hx j)
  · intro i _ hij
    rw [internalProj_of_mem_ne hW hij (hx i)]
    rfl
  · simp

end InternalProj

section Cyclic

variable {r : ℕ} [NeZero r] {t : V →ₗ[R] V} {W : ZMod r → Submodule R V}

private theorem sum_zmod_val_eq_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ j : ZMod r, f j.val = ∑ i ∈ Finset.range r, f i := by
  refine Finset.sum_nbij' (i := fun (a : ZMod r) => a.val)
    (j := fun (n : ℕ) => (n : ZMod r)) ?_ ?_ ?_ ?_ ?_
  · intro a _; simpa using ZMod.val_lt a
  · intro n _; simp
  · intro a _; simp
  · intro n hn
    simp only [Finset.mem_range] at hn
    rw [ZMod.val_natCast_of_lt hn]
  · intro a _; rfl

omit [NeZero r] in
private theorem pow_eq_pow_mod_of_pow_eq_one (ht : t ^ r = 1) (n : ℕ) : t ^ n = t ^ (n % r) := by
  conv_lhs => rw [← Nat.div_add_mod n r, pow_add, pow_mul, ht, one_pow, one_mul]

omit [NeZero r] in
theorem pow_apply_mem_of_map_eq (hmap : ∀ i, (W i).map t = W (i + 1)) {i : ZMod r} {x : V}
    (hx : x ∈ W i) (n : ℕ) : (t ^ n) x ∈ W (i + n) := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
      have h : t ((t ^ n) x) ∈ W ((i + n) + 1) := by
        rw [← hmap]; exact Submodule.mem_map_of_mem ih
      have hi : (i + (n : ZMod r)) + 1 = i + ((n + 1 : ℕ) : ZMod r) := by push_cast; ring
      rw [hi] at h
      simpa [pow_succ'] using h

theorem sum_pow_apply_mem_fixedSubmodule (ht : t ^ r = 1) (v : V) :
    (∑ i ∈ Finset.range r, (t ^ i) v) ∈ t.fixedSubmodule := by
  rw [LinearMap.mem_fixedSubmodule_iff, ← sum_zmod_val_eq_sum_range (fun i => (t ^ i) v), map_sum]
  have key : ∀ j : ZMod r, t ((t ^ j.val) v) = (t ^ (j + 1).val) v := by
    intro j
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod,
      ← pow_eq_pow_mod_of_pow_eq_one ht, pow_succ']
    rfl
  simp only [key]
  exact Equiv.sum_comp (Equiv.addRight (1 : ZMod r)) (fun j => (t ^ j.val) v)

theorem internalProj_succ_of_fixed (hW : IsInternal W) (hmap : ∀ i, (W i).map t = W (i + 1))
    {v : V} (hv : t v = v) (i : ZMod r) :
    (internalProj hW (i + 1) v : V) = t (internalProj hW i v : V) := by
  set w : ZMod r → V := fun j => (internalProj hW j v : V) with hw
  have hz : ∀ j : ZMod r, t (w (j - 1)) ∈ W j := by
    intro j
    have h := Submodule.mem_map_of_mem (f := t) (internalProj hW (j - 1) v).2
    rw [hmap] at h
    simpa using h
  have hsum : ∑ j : ZMod r, t (w (j - 1)) = v := by
    have h1 : ∑ j : ZMod r, t (w (j - 1)) = ∑ j : ZMod r, t (w j) :=
      Equiv.sum_comp (Equiv.subRight (1 : ZMod r)) (fun j => t (w j))
    rw [h1, ← map_sum, hw]
    simp only []
    rw [sum_internalProj hW v, hv]
  have h2 := internalProj_sum_of_mem hW (x := fun j => t (w (j - 1))) hz (i + 1)
  rw [hsum] at h2
  simpa using h2

theorem internalProj_natCast_of_fixed (hW : IsInternal W) (hmap : ∀ i, (W i).map t = W (i + 1))
    {v : V} (hv : t v = v) (n : ℕ) :
    (internalProj hW (n : ZMod r) v : V) = (t ^ n) (internalProj hW 0 v : V) := by
  induction n with
  | zero => rw [Nat.cast_zero, pow_zero]; rfl
  | succ n ih =>
      have h : ((n + 1 : ℕ) : ZMod r) = (n : ZMod r) + 1 := by push_cast; ring
      rw [h, internalProj_succ_of_fixed hW hmap hv, ih, pow_succ']
      rfl

theorem internalProj_zero_sum_pow (hW : IsInternal W) (hmap : ∀ i, (W i).map t = W (i + 1))
    {w : V} (hw : w ∈ W 0) :
    (internalProj hW 0 (∑ i ∈ Finset.range r, (t ^ i) w) : V) = w := by
  rw [← sum_zmod_val_eq_sum_range (fun i => (t ^ i) w)]
  have hmem : ∀ j : ZMod r, (t ^ j.val) w ∈ W j := by
    intro j
    have h := pow_apply_mem_of_map_eq hmap hw j.val
    simpa using h
  rw [internalProj_sum_of_mem hW hmem 0, ZMod.val_zero, pow_zero]
  rfl

theorem sum_pow_internalProj_zero (hW : IsInternal W) (hmap : ∀ i, (W i).map t = W (i + 1))
    {v : V} (hv : t v = v) :
    ∑ i ∈ Finset.range r, (t ^ i) (internalProj hW 0 v : V) = v := by
  rw [← sum_zmod_val_eq_sum_range (fun i => (t ^ i) (internalProj hW 0 v : V))]
  have key : ∀ j : ZMod r, (t ^ j.val) (internalProj hW 0 v : V) = (internalProj hW j v : V) := by
    intro j
    rw [← internalProj_natCast_of_fixed hW hmap hv j.val, ZMod.natCast_val, ZMod.cast_id]
  simp only [key]
  exact sum_internalProj hW v

noncomputable def fixedSubmoduleEquivOfCyclicOrbit (hW : IsInternal W)
    (hmap : ∀ i, (W i).map t = W (i + 1)) (ht : t ^ r = 1) :
    t.fixedSubmodule ≃ₗ[R] W 0 :=
  LinearEquiv.ofLinearMap ((internalProj hW 0).comp t.fixedSubmodule.subtype)
    (((∑ i ∈ Finset.range r, t ^ i).comp (W 0).subtype).codRestrict t.fixedSubmodule
      (fun w => by
        simpa [LinearMap.sum_apply] using sum_pow_apply_mem_fixedSubmodule ht (w : V)))
    (by
      ext w
      simpa [LinearMap.sum_apply] using internalProj_zero_sum_pow hW hmap w.2)
    (by
      ext v
      simpa [LinearMap.sum_apply] using
        sum_pow_internalProj_zero hW hmap (LinearMap.mem_fixedSubmodule_iff.1 v.2))

@[simp]
theorem fixedSubmoduleEquivOfCyclicOrbit_apply (hW : IsInternal W)
    (hmap : ∀ i, (W i).map t = W (i + 1)) (ht : t ^ r = 1) (v : t.fixedSubmodule) :
    fixedSubmoduleEquivOfCyclicOrbit hW hmap ht v = internalProj hW 0 (v : V) := (rfl)

@[simp]
theorem fixedSubmoduleEquivOfCyclicOrbit_symm_apply (hW : IsInternal W)
    (hmap : ∀ i, (W i).map t = W (i + 1)) (ht : t ^ r = 1) (w : W 0) :
    ((fixedSubmoduleEquivOfCyclicOrbit hW hmap ht).symm w : V)
      = ∑ i ∈ Finset.range r, (t ^ i) (w : V) := by
  simp [fixedSubmoduleEquivOfCyclicOrbit]

theorem finrank_fixedSubmodule_of_cyclicOrbit (hW : IsInternal W)
    (hmap : ∀ i, (W i).map t = W (i + 1)) (ht : t ^ r = 1) :
    Module.finrank R t.fixedSubmodule = Module.finrank R (W 0) :=
  (fixedSubmoduleEquivOfCyclicOrbit hW hmap ht).finrank_eq

theorem rank_fixedSubmodule_of_cyclicOrbit (hW : IsInternal W)
    (hmap : ∀ i, (W i).map t = W (i + 1)) (ht : t ^ r = 1) :
    Module.rank R t.fixedSubmodule = Module.rank R (W 0) :=
  (fixedSubmoduleEquivOfCyclicOrbit hW hmap ht).rank_eq

end Cyclic

end CFSG.FeitThompson
