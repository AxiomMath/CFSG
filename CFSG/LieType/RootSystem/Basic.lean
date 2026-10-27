module

public import Mathlib.GroupTheory.Coxeter.Basic
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Basic
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Matrix

public section

namespace CFSG.LieType.RootSystem

variable {I : Type} [Fintype I] [DecidableEq I]

@[expose] def coroot (A : Matrix I I ℤ) (i : I) : (I → ℤ) →ₗ[ℤ] ℤ :=
  ∑ j, A i j • LinearMap.proj j

omit [DecidableEq I] in
theorem coroot_apply (A : Matrix I I ℤ) (i : I) (v : I → ℤ) :
    coroot A i v = ∑ j, A i j * v j := by
  simp [coroot]

theorem coroot_single (A : Matrix I I ℤ) (i j : I) : coroot A i (Pi.single j 1) = A i j := by
  simp [coroot_apply, Pi.single_apply]

@[expose] def reflection (A : Matrix I I ℤ) (i : I) : Module.End ℤ (I → ℤ) :=
  LinearMap.id - (coroot A i).smulRight (Pi.single i 1)

theorem reflection_apply (A : Matrix I I ℤ) (i : I) (v : I → ℤ) :
    reflection A i v = v - (∑ j, A i j * v j) • Pi.single i 1 := by
  simp [reflection, coroot_apply]

theorem reflection_apply_coroot (A : Matrix I I ℤ) (i : I) (v : I → ℤ) :
    reflection A i v = v - coroot A i v • Pi.single i 1 := by
  simp [reflection]

theorem reflection_apply_of_ne (A : Matrix I I ℤ) {i k : I} (h : k ≠ i) (v : I → ℤ) :
    reflection A i v k = v k := by
  simp [reflection_apply_coroot, h]

theorem coroot_reflection {A : Matrix I I ℤ} {i : I} (h : A i i = 2) (v : I → ℤ) :
    coroot A i (reflection A i v) = -coroot A i v := by
  rw [reflection_apply_coroot, map_sub, map_zsmul, coroot_single, h]
  simp only [smul_eq_mul]
  ring

theorem reflection_single_self {A : Matrix I I ℤ} {i : I} (h : A i i = 2) :
    reflection A i (Pi.single i 1) = -Pi.single i 1 := by
  rw [reflection_apply_coroot, coroot_single, h]
  module

theorem reflection_mul_self {A : Matrix I I ℤ} {i : I} (h : A i i = 2) :
    reflection A i * reflection A i = 1 := by
  refine LinearMap.ext fun v => ?_
  rw [Module.End.mul_apply, reflection_apply_coroot A i (reflection A i v), coroot_reflection h,
    reflection_apply_coroot, Module.End.one_apply]
  simp

section RankTwo

def pair (i j : I) : ℤ × ℤ →ₗ[ℤ] (I → ℤ) :=
  (LinearMap.fst ℤ ℤ ℤ).smulRight (Pi.single i 1) +
    (LinearMap.snd ℤ ℤ ℤ).smulRight (Pi.single j 1)

omit [Fintype I] in
theorem pair_apply (i j : I) (z : ℤ × ℤ) :
    pair i j z = z.1 • Pi.single i 1 + z.2 • Pi.single j 1 := by
  simp [pair]

theorem reflection_pair_left {A : Matrix I I ℤ} {i : I} (j : I) (h : A i i = 2) (z : ℤ × ℤ) :
    reflection A i (pair i j z) = pair i j (-z.1 - A i j * z.2, z.2) := by
  rw [pair_apply, reflection_apply_coroot, map_add, map_zsmul, map_zsmul, coroot_single,
    coroot_single, h, pair_apply]
  module

theorem reflection_pair_right {A : Matrix I I ℤ} (i : I) {j : I} (h : A j j = 2) (z : ℤ × ℤ) :
    reflection A j (pair i j z) = pair i j (z.1, -z.2 - A j i * z.1) := by
  rw [pair_apply, reflection_apply_coroot, map_add, map_zsmul, map_zsmul, coroot_single,
    coroot_single, h, pair_apply]
  module

private def rot (a b : ℤ) (z : ℤ × ℤ) : ℤ × ℤ := ((a * b - 1) * z.1 + a * z.2, -b * z.1 - z.2)

private theorem reflection_mul_reflection_pair {A : Matrix I I ℤ} {i j : I} (hi : A i i = 2)
    (hj : A j j = 2) (z : ℤ × ℤ) :
    (reflection A i * reflection A j) (pair i j z) = pair i j (rot (A i j) (A j i) z) := by
  rw [Module.End.mul_apply, reflection_pair_right i hj, reflection_pair_left j hi]
  simp only [rot]
  congr 2 <;> ring

private theorem pow_pair {A : Matrix I I ℤ} {i j : I} (hi : A i i = 2) (hj : A j j = 2) (k : ℕ)
    (z : ℤ × ℤ) :
    ((reflection A i * reflection A j) ^ k) (pair i j z) =
      pair i j ((rot (A i j) (A j i))^[k] z) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, reflection_mul_reflection_pair hi hj,
      Function.iterate_succ_apply']

omit [Fintype I] [DecidableEq I] in
private theorem geom_sum_apply_sub {M : Type*} [AddCommGroup M] (f : Module.End ℤ M) (m : ℕ)
    (v : M) : (∑ k ∈ Finset.range m, f ^ k) (f v - v) = (f ^ m) v - v := by
  have := congrArg (fun g : Module.End ℤ M => g v) (geom_sum_mul f m)
  simpa [Module.End.mul_apply] using this

private theorem pow_eq_one_of_sum {A : Matrix I I ℤ} {i j : I} (hi : A i i = 2) (hj : A j j = 2)
    (m : ℕ) (hm : ∀ z : ℤ × ℤ, ∑ k ∈ Finset.range m, (rot (A i j) (A j i))^[k] z = 0) :
    (reflection A i * reflection A j) ^ m = 1 := by
  refine LinearMap.ext fun v => ?_
  have hv : (reflection A i * reflection A j) v - v =
      pair i j (-coroot A i (reflection A j v), -coroot A j v) := by
    rw [Module.End.mul_apply, reflection_apply_coroot A i, reflection_apply_coroot A j,
      pair_apply]
    simp only [neg_smul]
    abel
  rw [Module.End.one_apply, ← sub_eq_zero, ← geom_sum_apply_sub, hv, LinearMap.sum_apply]
  simp only [pow_pair hi hj]
  rw [← map_sum, hm, map_zero]

private theorem int_pair_cases {a b : ℤ} (ha : a ≤ 0) (hb : b ≤ 0) (hab : a = 0 ↔ b = 0)
    (h : a * b ∈ ({0, 1, 2, 3} : Set ℤ)) :
    (a = 0 ∧ b = 0) ∨ (a = -1 ∧ b = -1) ∨ (a = -1 ∧ b = -2) ∨ (a = -2 ∧ b = -1) ∨
      (a = -1 ∧ b = -3) ∨ (a = -3 ∧ b = -1) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  have h3 : a * b ≤ 3 := by omega
  rcases eq_or_lt_of_le ha with rfl | ha'
  · simp_all
  have hb' : b < 0 := lt_of_le_of_ne hb fun h => absurd (hab.mpr h) ha'.ne
  have hab1 : -3 ≤ a := by nlinarith
  have hab2 : -3 ≤ b := by nlinarith
  interval_cases a <;> interval_cases b <;> simp_all

end RankTwo

variable {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A)

omit [DecidableEq I] in
include hA in
theorem cartan_pair_cases {i j : I} (hij : i ≠ j) :
    (A i j = 0 ∧ A j i = 0) ∨ (A i j = -1 ∧ A j i = -1) ∨ (A i j = -1 ∧ A j i = -2) ∨
      (A i j = -2 ∧ A j i = -1) ∨ (A i j = -1 ∧ A j i = -3) ∨ (A i j = -3 ∧ A j i = -1) :=
  int_pair_cases (hA.apply_le_zero_of_ne hij) (hA.apply_le_zero_of_ne hij.symm)
    hA.apply_eq_zero_iff (hA.apply_mul_apply_mem_of_ne hij)

abbrev coxeterMatrix : CoxeterMatrix I :=
  TauCeti.coxeterMatrixOfCartanMatrix A hA.apply_self fun _ _ h => hA.apply_mul_apply_mem_of_ne h

theorem isLiftable : (coxeterMatrix hA).IsLiftable (reflection A) := by
  intro i j
  simp only [coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply]
  rcases eq_or_ne i j with rfl | hij
  · rw [hA.apply_self, (by norm_num : (2 : ℤ) * 2 = 4), TauCeti.coxeterOrder_four, pow_one]
    exact reflection_mul_self (hA.apply_self i)
  refine pow_eq_one_of_sum (hA.apply_self i) (hA.apply_self j) _ ?_
  rcases cartan_pair_cases hA hij with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ <;>
  · rw [h1, h2]
    intro z
    norm_num [Finset.sum_range_succ, Function.iterate_succ_apply', rot]
    ext <;> simp <;> ring

@[expose] noncomputable def weylAction : (coxeterMatrix hA).Group →* Module.End ℤ (I → ℤ) :=
  (coxeterMatrix hA).toCoxeterSystem.lift ⟨reflection A, isLiftable hA⟩

theorem weylAction_simple (i : I) :
    weylAction hA ((coxeterMatrix hA).toCoxeterSystem.simple i) = reflection A i :=
  (coxeterMatrix hA).toCoxeterSystem.lift_apply_simple (isLiftable hA) i

@[expose] def roots (D : Set I) : Set (I → ℤ) :=
  {γ | ∃ (w : (coxeterMatrix hA).Group) (i : I), γ = weylAction hA w (Pi.single i 1)} ∪
    {γ | ∃ (w : (coxeterMatrix hA).Group), ∃ i ∈ D, γ = 2 • weylAction hA w (Pi.single i 1)}

theorem weylAction_mul_apply (w w' : (coxeterMatrix hA).Group) (v : I → ℤ) :
    weylAction hA (w * w') v = weylAction hA w (weylAction hA w' v) := by
  rw [map_mul, Module.End.mul_apply]

theorem weylAction_inv_apply_apply (w : (coxeterMatrix hA).Group) (v : I → ℤ) :
    weylAction hA w⁻¹ (weylAction hA w v) = v := by
  rw [← weylAction_mul_apply, inv_mul_cancel, map_one, Module.End.one_apply]

theorem weylAction_apply_inv_apply (w : (coxeterMatrix hA).Group) (v : I → ℤ) :
    weylAction hA w (weylAction hA w⁻¹ v) = v := by
  rw [← weylAction_mul_apply, mul_inv_cancel, map_one, Module.End.one_apply]

theorem weylAction_apply_injective (w : (coxeterMatrix hA).Group) :
    Function.Injective (weylAction hA w) := fun u v h => by
  rw [← weylAction_inv_apply_apply hA w u, h, weylAction_inv_apply_apply]

theorem weylAction_single_ne_zero (w : (coxeterMatrix hA).Group) (i : I) :
    weylAction hA w (Pi.single i 1) ≠ 0 := by
  rw [← map_zero (weylAction hA w), Ne, (weylAction_apply_injective hA w).eq_iff]
  simp

theorem weylAction_simple_single (i : I) :
    weylAction hA ((coxeterMatrix hA).toCoxeterSystem.simple i) (Pi.single i 1) =
      -Pi.single i 1 := by
  rw [weylAction_simple, reflection_single_self (hA.apply_self i)]

theorem weylAction_simple_apply_of_ne (i : I) (v : I → ℤ) {j : I} (h : j ≠ i) :
    weylAction hA ((coxeterMatrix hA).toCoxeterSystem.simple i) v j = v j := by
  rw [weylAction_simple, reflection_apply_of_ne A h]

end CFSG.LieType.RootSystem
