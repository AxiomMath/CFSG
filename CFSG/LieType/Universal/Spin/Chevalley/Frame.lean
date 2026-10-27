module

public import CFSG.LieType.Universal.Spin.Chevalley.Basic

public section

namespace CFSG.LieType.Universal.Spin

open CliffordAlgebra QuadraticMap

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {n : ℕ}

structure HypFrame (Q : QuadraticForm K V) (n : ℕ) where
  vec : Fin n → Bool → V
  map_vec : ∀ i s, Q (vec i s) = 0
  polar_vec_of_ne : ∀ ⦃i j : Fin n⦄, i ≠ j → ∀ s t, polar Q (vec i s) (vec j t) = 0
  polar_vec_not : ∀ i s, polar Q (vec i s) (vec i (!s)) = 1
  exists_aux : ∀ i j : Fin n, ∃ a : V, IsUnit (Q a) ∧
    ∀ s, polar Q (vec i s) a = 0 ∧ polar Q (vec j s) a = 0

structure OddFrame (Q : QuadraticForm K V) (n : ℕ) extends HypFrame Q n where
  z : V
  map_z : Q z = 1
  polar_vec_z : ∀ i s, polar Q (vec i s) z = 0

attribute [simp] HypFrame.map_vec HypFrame.polar_vec_not OddFrame.map_z OddFrame.polar_vec_z

namespace HypFrame

variable (F : HypFrame Q n)

@[simp]
theorem polar_vec_self (i : Fin n) (s : Bool) : polar Q (F.vec i s) (F.vec i s) = 0 := by
  rw [QuadraticMap.polar_self, F.map_vec, smul_zero]

@[simp]
theorem polar_not_vec (i : Fin n) (s : Bool) : polar Q (F.vec i (!s)) (F.vec i s) = 1 := by
  rw [polar_comm, F.polar_vec_not]

theorem polar_vec_vec (i j : Fin n) (s t : Bool) :
    polar Q (F.vec i s) (F.vec j t) = if i = j ∧ s = !t then 1 else 0 := by
  by_cases hij : i = j
  · subst hij
    by_cases hst : s = !t
    · rw [ite_eq_left ⟨rfl, hst⟩, hst, F.polar_not_vec]
    · have hst' : s = t := by cases s <;> cases t <;> simp_all
      rw [ite_eq_right fun h => hst h.2, hst', F.polar_vec_self]
  · rw [F.polar_vec_of_ne hij, ite_eq_right fun h => hij h.1]

theorem linearIndependent_vec (σ : Fin n → Bool) :
    LinearIndependent K fun m => F.vec m (σ m) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg m
  have h := congrArg (fun v => polarBilin Q v (F.vec m (!σ m))) hg
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, polarBilin_apply_apply,
    map_zero, LinearMap.zero_apply, smul_eq_mul] at h
  rwa [Finset.sum_eq_single m (fun b _ hb => by rw [F.polar_vec_of_ne hb, mul_zero])
    (fun h' => absurd (Finset.mem_univ m) h'), F.polar_vec_not, mul_one] at h

theorem linearIndependent_vec_pair {i j : Fin n} (hij : i ≠ j) (s t : Bool) :
    LinearIndependent K ![F.vec i s, F.vec j t] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have h1 := congrArg (fun v => polar Q v (F.vec i (!s))) hab
  have h2 := congrArg (fun v => polar Q v (F.vec j (!t))) hab
  simp only [polar_add_left, polar_smul_left, smul_eq_mul, polar_zero_left, F.polar_vec_not,
    F.polar_vec_of_ne hij, F.polar_vec_of_ne hij.symm, mul_zero, mul_one, add_zero,
    zero_add] at h1 h2
  exact ⟨h1, h2⟩

@[simp]
theorem ι_vec_mul_ι_vec_self (i : Fin n) (s : Bool) :
    ι Q (F.vec i s) * ι Q (F.vec i s) = 0 :=
  ι_mul_ι_self_eq_zero Q (F.map_vec i s)

@[simp]
theorem ι_vec_mul_ι_vec_self_mul (i : Fin n) (s : Bool) (x : CliffordAlgebra Q) :
    ι Q (F.vec i s) * (ι Q (F.vec i s) * x) = 0 :=
  ι_mul_ι_mul_eq_zero Q (F.map_vec i s) x

theorem ι_vec_mul_ι_vec_of_ne {i j : Fin n} (hij : i ≠ j) (s t : Bool) :
    ι Q (F.vec i s) * ι Q (F.vec j t) = -(ι Q (F.vec j t) * ι Q (F.vec i s)) :=
  ι_mul_ι_eq_neg_of_polar_eq_zero Q (F.polar_vec_of_ne hij s t)

theorem ι_vec_mul_ι_vec_not_add (i : Fin n) (s : Bool) :
    ι Q (F.vec i s) * ι Q (F.vec i (!s)) + ι Q (F.vec i (!s)) * ι Q (F.vec i s) = 1 :=
  ι_mul_ι_add_ι_mul_ι_eq_one Q (F.polar_vec_not i s)

theorem ι_vec_mul_ι_vec_not_mul_ι_vec (i : Fin n) (s : Bool) :
    ι Q (F.vec i s) * (ι Q (F.vec i (!s)) * ι Q (F.vec i s)) = ι Q (F.vec i s) :=
  ι_mul_ι_mul_ι_eq_self Q (F.map_vec i s) (F.polar_vec_not i s)

theorem one_add_smul_mem_spinGroup {i j : Fin n} (hij : i ≠ j) (s t : Bool) (c : K) :
    1 + c • (ι Q (F.vec i s) * ι Q (F.vec j t)) ∈ spinGroup Q := by
  obtain ⟨a, ha, h⟩ := F.exists_aux i j
  exact one_add_smul_ι_mul_ι_mem_spinGroup Q (F.map_vec j t) (F.polar_vec_of_ne hij.symm t s)
    (h t).2 (h s).1 ha c

noncomputable def longRoot {i j : Fin n} (hij : i ≠ j) (s t : Bool) :
    Multiplicative K →* spinGroup Q :=
  rootHom Q (F.map_vec j t) (F.polar_vec_of_ne hij.symm t s) (F.one_add_smul_mem_spinGroup hij s t)

theorem coe_longRoot {i j : Fin n} (hij : i ≠ j) (s t : Bool) (c : K) :
    (F.longRoot hij s t (.ofAdd c) : CliffordAlgebra Q) =
      1 + c • (ι Q (F.vec i s) * ι Q (F.vec j t)) :=
  coe_rootHom Q _ _ _ c

theorem longRoot_swap {i j : Fin n} (hij : i ≠ j) (s t : Bool) (c : K) :
    F.longRoot hij s t (.ofAdd c) = F.longRoot hij.symm t s (.ofAdd (-c)) := by
  apply Subtype.ext
  rw [coe_longRoot, coe_longRoot, F.ι_vec_mul_ι_vec_of_ne hij, smul_neg, neg_smul]

theorem longRoot_injective {i j : Fin n} (hij : i ≠ j) (s t : Bool) :
    Function.Injective (F.longRoot hij s t) :=
  rootHom_injective Q _ _ _ (F.linearIndependent_vec_pair hij s t)

theorem spinAction_longRoot {i j : Fin n} (hij : i ≠ j) (s t : Bool) (c : K) (v : V) :
    spinAction Q (F.longRoot hij s t (.ofAdd c)) v =
      v + (c * polar Q v (F.vec j t)) • F.vec i s - (c * polar Q v (F.vec i s)) • F.vec j t := by
  rw [longRoot, spinAction_rootHom]
  simp only [QuadraticMap.map_smul, F.map_vec, polar_smul_right, smul_eq_mul, mul_zero, zero_mul]
  module

theorem spinAction_longRoot_of_polar {i j : Fin n} (hij : i ≠ j) (s t : Bool) (c : K) {v : V}
    (hi : polar Q v (F.vec i s) = 0) (hj : polar Q v (F.vec j t) = 0) :
    spinAction Q (F.longRoot hij s t (.ofAdd c)) v = v := by
  rw [spinAction_longRoot, hi, hj, mul_zero, zero_smul, zero_smul, add_zero, sub_zero]

theorem spinAction_longRoot_vec_of_ne {i j : Fin n} (hij : i ≠ j) (s t : Bool) (c : K)
    {k : Fin n} (hki : k ≠ i) (hkj : k ≠ j) (u : Bool) :
    spinAction Q (F.longRoot hij s t (.ofAdd c)) (F.vec k u) = F.vec k u :=
  F.spinAction_longRoot_of_polar hij s t c (F.polar_vec_of_ne hki u s) (F.polar_vec_of_ne hkj u t)

@[simp]
theorem spinAction_longRoot_vec_left {i j : Fin n} (hij : i ≠ j) (s t : Bool) (c : K) :
    spinAction Q (F.longRoot hij s t (.ofAdd c)) (F.vec i s) = F.vec i s :=
  F.spinAction_longRoot_of_polar hij s t c (F.polar_vec_self i s) (F.polar_vec_of_ne hij s t)

@[simp]
theorem spinAction_longRoot_vec_right {i j : Fin n} (hij : i ≠ j) (s t : Bool) (c : K) :
    spinAction Q (F.longRoot hij s t (.ofAdd c)) (F.vec j t) = F.vec j t :=
  F.spinAction_longRoot_of_polar hij s t c (F.polar_vec_of_ne hij.symm t s) (F.polar_vec_self j t)

@[simp]
theorem spinAction_longRoot_vec_not_left {i j : Fin n} (hij : i ≠ j) (s t : Bool) (c : K) :
    spinAction Q (F.longRoot hij s t (.ofAdd c)) (F.vec i (!s)) = F.vec i (!s) - c • F.vec j t := by
  rw [spinAction_longRoot, F.polar_vec_of_ne hij, polar_not_vec, mul_zero, zero_smul, add_zero,
    mul_one]

@[simp]
theorem spinAction_longRoot_vec_not_right {i j : Fin n} (hij : i ≠ j) (s t : Bool) (c : K) :
    spinAction Q (F.longRoot hij s t (.ofAdd c)) (F.vec j (!t)) =
      F.vec j (!t) + c • F.vec i s := by
  rw [spinAction_longRoot, F.polar_vec_of_ne hij.symm, polar_not_vec, mul_zero, zero_smul,
    sub_zero, mul_one]

end HypFrame

namespace OddFrame

variable (F : OddFrame Q n)

@[expose] def ofZ (vec : Fin n → Bool → V) (map_vec : ∀ i s, Q (vec i s) = 0)
    (polar_vec_of_ne : ∀ ⦃i j : Fin n⦄, i ≠ j → ∀ s t, polar Q (vec i s) (vec j t) = 0)
    (polar_vec_not : ∀ i s, polar Q (vec i s) (vec i (!s)) = 1) (z : V) (map_z : Q z = 1)
    (polar_vec_z : ∀ i s, polar Q (vec i s) z = 0) : OddFrame Q n where
  vec := vec
  map_vec := map_vec
  polar_vec_of_ne := polar_vec_of_ne
  polar_vec_not := polar_vec_not
  exists_aux _ _ := ⟨z, by rw [map_z]; exact isUnit_one, fun s => ⟨polar_vec_z _ s, polar_vec_z _ s⟩⟩
  z := z
  map_z := map_z
  polar_vec_z := polar_vec_z

@[simp]
theorem polar_z_vec (i : Fin n) (s : Bool) : polar Q F.z (F.vec i s) = 0 := by
  rw [polar_comm, F.polar_vec_z]

@[simp]
theorem polar_z_self : polar Q F.z F.z = 2 := by
  rw [QuadraticMap.polar_self, F.map_z, nsmul_eq_mul, mul_one, Nat.cast_ofNat]

@[simp]
theorem ι_z_mul_ι_z : ι Q F.z * ι Q F.z = 1 := by
  rw [ι_sq_scalar, F.map_z, map_one]

theorem ι_vec_mul_ι_z (i : Fin n) (s : Bool) :
    ι Q (F.vec i s) * ι Q F.z = -(ι Q F.z * ι Q (F.vec i s)) :=
  ι_mul_ι_eq_neg_of_polar_eq_zero Q (F.polar_vec_z i s)

theorem ι_z_mul_ι_vec (i : Fin n) (s : Bool) :
    ι Q F.z * ι Q (F.vec i s) = -(ι Q (F.vec i s) * ι Q F.z) := by
  rw [F.ι_vec_mul_ι_z, neg_neg]

theorem linearIndependent_z_vec (i : Fin n) (s : Bool) :
    LinearIndependent K ![F.z, F.vec i s] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have h1 := congrArg (fun v => polar Q v (F.vec i (!s))) hab
  simp only [polar_add_left, polar_smul_left, smul_eq_mul, polar_zero_left,
    F.polar_vec_not, polar_z_vec, mul_zero, mul_one, zero_add] at h1
  refine ⟨?_, h1⟩
  rw [h1, zero_smul, add_zero] at hab
  have hz : F.z ≠ 0 := fun h => by simpa [h] using F.map_z
  exact (smul_eq_zero.mp hab).resolve_right hz

theorem one_add_smul_z_mem_spinGroup (i : Fin n) (s : Bool) (c : K) :
    1 + c • (ι Q F.z * ι Q (F.vec i s)) ∈ spinGroup Q :=
  one_add_smul_ι_mul_ι_mem_spinGroup_of_isUnit Q (F.map_vec i s) (F.polar_vec_z i s)
    (by rw [F.map_z]; exact isUnit_one) c

noncomputable def shortRoot (i : Fin n) (s : Bool) : Multiplicative K →* spinGroup Q :=
  rootHom Q (F.map_vec i s) (F.polar_vec_z i s) (F.one_add_smul_z_mem_spinGroup i s)

theorem coe_shortRoot (i : Fin n) (s : Bool) (c : K) :
    (F.shortRoot i s (.ofAdd c) : CliffordAlgebra Q) = 1 + c • (ι Q F.z * ι Q (F.vec i s)) :=
  coe_rootHom Q _ _ _ c

theorem shortRoot_injective (i : Fin n) (s : Bool) : Function.Injective (F.shortRoot i s) :=
  rootHom_injective Q _ _ _ (F.linearIndependent_z_vec i s)

theorem spinAction_shortRoot (i : Fin n) (s : Bool) (c : K) (v : V) :
    spinAction Q (F.shortRoot i s (.ofAdd c)) v =
      v + (c * polar Q v (F.vec i s)) • F.z -
        (c * polar Q v F.z + c ^ 2 * polar Q v (F.vec i s)) • F.vec i s := by
  rw [shortRoot, spinAction_rootHom]
  simp only [QuadraticMap.map_smul, F.map_z, polar_smul_right, smul_eq_mul, mul_one]
  module

theorem spinAction_shortRoot_of_polar (i : Fin n) (s : Bool) (c : K) {v : V}
    (hi : polar Q v (F.vec i s) = 0) (hz : polar Q v F.z = 0) :
    spinAction Q (F.shortRoot i s (.ofAdd c)) v = v := by
  rw [spinAction_shortRoot, hi, hz]
  simp

theorem spinAction_shortRoot_vec_of_ne (i : Fin n) (s : Bool) (c : K) {k : Fin n} (hki : k ≠ i)
    (u : Bool) : spinAction Q (F.shortRoot i s (.ofAdd c)) (F.vec k u) = F.vec k u :=
  F.spinAction_shortRoot_of_polar i s c (F.polar_vec_of_ne hki u s) (F.polar_vec_z k u)

@[simp]
theorem spinAction_shortRoot_vec_self (i : Fin n) (s : Bool) (c : K) :
    spinAction Q (F.shortRoot i s (.ofAdd c)) (F.vec i s) = F.vec i s :=
  F.spinAction_shortRoot_of_polar i s c (F.polar_vec_self i s) (F.polar_vec_z i s)

@[simp]
theorem spinAction_shortRoot_vec_not (i : Fin n) (s : Bool) (c : K) :
    spinAction Q (F.shortRoot i s (.ofAdd c)) (F.vec i (!s)) =
      F.vec i (!s) + c • F.z - c ^ 2 • F.vec i s := by
  rw [spinAction_shortRoot, HypFrame.polar_not_vec, F.polar_vec_z]
  simp

@[simp]
theorem spinAction_shortRoot_z (i : Fin n) (s : Bool) (c : K) :
    spinAction Q (F.shortRoot i s (.ofAdd c)) F.z = F.z - (2 * c) • F.vec i s := by
  rw [spinAction_shortRoot, polar_z_vec, polar_z_self]
  simp [mul_comm]

@[simp]
theorem spinAction_longRoot_z {i j : Fin n} (hij : i ≠ j) (s t : Bool) (c : K) :
    spinAction Q (F.longRoot hij s t (.ofAdd c)) F.z = F.z :=
  F.spinAction_longRoot_of_polar hij s t c (F.polar_z_vec i s) (F.polar_z_vec j t)

end OddFrame

end CFSG.LieType.Universal.Spin
