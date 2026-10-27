module

public import CFSG.LieType.Universal.Spin.Chevalley.Commutator

public section

namespace CFSG.LieType.Universal.Spin

open CliffordAlgebra QuadraticMap

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {n : ℕ}

namespace HypFrame

variable (F : HypFrame Q n)

@[expose] noncomputable def longPair {i j : Fin n} (hij : i ≠ j) (s t : Bool) :
    SL2Pair (CliffordAlgebra Q) where
  X := ι Q (F.vec i s) * ι Q (F.vec j t)
  Y := ι Q (F.vec j (!t)) * ι Q (F.vec i (!s))
  X_mul_X := ι_mul_ι_mul_ι_mul_ι_eq_zero Q (F.map_vec j t) (F.polar_vec_of_ne hij.symm t s)
  Y_mul_Y := ι_mul_ι_mul_ι_mul_ι_eq_zero Q (F.map_vec i (!s)) (F.polar_vec_of_ne hij (!s) (!t))
  X_mul_Y_mul_X := ι_mul_ι_mul_ι_mul_ι_mul_ι_mul_ι Q (F.map_vec i s) (F.map_vec j t)
    (F.polar_vec_not i s) (F.polar_vec_not j t) (F.polar_vec_of_ne hij.symm t s)
    (F.polar_vec_of_ne hij.symm t (!s)) (F.polar_vec_of_ne hij.symm (!t) s)
    (F.polar_vec_of_ne hij.symm (!t) (!s))
  Y_mul_X_mul_Y := by
    have h := ι_mul_ι_mul_ι_mul_ι_mul_ι_mul_ι Q (F.map_vec j (!t)) (F.map_vec i (!s))
      (F.polar_vec_not j (!t)) (F.polar_vec_not i (!s)) (F.polar_vec_of_ne hij (!s) (!t))
      (F.polar_vec_of_ne hij (!s) (!(!t))) (F.polar_vec_of_ne hij (!(!s)) (!t))
      (F.polar_vec_of_ne hij (!(!s)) (!(!t)))
    simpa only [Bool.not_not] using h

@[expose] noncomputable def longSL2 {i j : Fin n} (hij : i ≠ j) (s t : Bool) :
    Matrix.SpecialLinearGroup (Fin 2) K →* spinGroup Q :=
  (F.longPair hij s t).toSpin (F.one_add_smul_mem_spinGroup hij s t)
    (F.one_add_smul_mem_spinGroup hij.symm (!t) (!s))

theorem coe_longSL2 {i j : Fin n} (hij : i ≠ j) (s t : Bool)
    (M : Matrix.SpecialLinearGroup (Fin 2) K) :
    (F.longSL2 hij s t M : CliffordAlgebra Q) =
      (F.longPair hij s t).toFun (M : Matrix (Fin 2) (Fin 2) K) := rfl

@[simp]
theorem longSL2_upperSL2 {i j : Fin n} (hij : i ≠ j) (s t : Bool) (c : K) :
    F.longSL2 hij s t (upperSL2 c) = F.longRoot hij s t (.ofAdd c) := by
  apply Subtype.ext
  rw [coe_longSL2, SL2Pair.toFun_upperSL2, coe_longRoot]
  rfl

@[simp]
theorem longSL2_lowerSL2 {i j : Fin n} (hij : i ≠ j) (s t : Bool) (c : K) :
    F.longSL2 hij s t (lowerSL2 c) = F.longRoot hij.symm (!t) (!s) (.ofAdd c) := by
  apply Subtype.ext
  rw [coe_longSL2, SL2Pair.toFun_lowerSL2, coe_longRoot]
  rfl

@[expose] noncomputable def longWeyl {i j : Fin n} (hij : i ≠ j) (s t : Bool) : spinGroup Q :=
  F.longSL2 hij s t (weylSL2 1)

theorem longWeyl_congr {i j i' j' : Fin n} (hij : i ≠ j) (hij' : i' ≠ j') (hi : i = i')
    (hj : j = j') {s t s' t' : Bool} (hs : s = s') (ht : t = t') :
    F.longWeyl hij s t = F.longWeyl hij' s' t' := by
  subst hi hj hs ht
  rfl

theorem longWeyl_eq {i j : Fin n} (hij : i ≠ j) (s t : Bool) :
    F.longWeyl hij s t = F.longRoot hij s t (.ofAdd 1) *
      F.longRoot hij.symm (!t) (!s) (.ofAdd (-1)) * F.longRoot hij s t (.ofAdd 1) := by
  rw [longWeyl, weylSL2_eq, map_mul, map_mul, longSL2_upperSL2, longSL2_lowerSL2]
  simp

@[expose] noncomputable def longTorus {i j : Fin n} (hij : i ≠ j) (s t : Bool) : Kˣ →* spinGroup Q :=
  (F.longSL2 hij s t).comp diagSL2

theorem longTorus_apply {i j : Fin n} (hij : i ≠ j) (s t : Bool) (τ : Kˣ) :
    F.longTorus hij s t τ = F.longSL2 hij s t (diagSL2 τ) := rfl

theorem longWeyl_mul_self {i j : Fin n} (hij : i ≠ j) (s t : Bool) :
    F.longWeyl hij s t * F.longWeyl hij s t = F.longTorus hij s t (-1) := by
  rw [longWeyl, ← map_mul, weylSL2_one_mul_self, longTorus_apply]

theorem longWeyl_mul_longTorus_mul_inv {i j : Fin n} (hij : i ≠ j) (s t : Bool) (τ : Kˣ) :
    F.longWeyl hij s t * F.longTorus hij s t τ * (F.longWeyl hij s t)⁻¹ =
      F.longTorus hij s t τ⁻¹ := by
  rw [longWeyl, longTorus_apply, longTorus_apply, ← map_inv, ← map_mul, ← map_mul,
    weylSL2_mul_diagSL2_mul_inv]

theorem spinAction_longSL2_weylSL2 {i j : Fin n} (hij : i ≠ j) (s t : Bool) (τ : Kˣ) (v : V) :
    spinAction Q (F.longSL2 hij s t (weylSL2 τ)) v =
      v + ((τ : K) * polar Q v (F.vec j t) - polar Q v (F.vec i (!s))) • F.vec i s
        + (((τ⁻¹ : Kˣ) : K) * polar Q v (F.vec j (!t)) - polar Q v (F.vec i s)) • F.vec i (!s)
        - (polar Q v (F.vec j (!t)) + (τ : K) * polar Q v (F.vec i s)) • F.vec j t
        - (polar Q v (F.vec j t) + ((τ⁻¹ : Kˣ) : K) * polar Q v (F.vec i (!s))) •
          F.vec j (!t) := by
  simp only [weylSL2_eq, map_mul, longSL2_upperSL2, longSL2_lowerSL2, LinearEquiv.mul_apply,
    spinAction_longRoot]
  simp only [polar_add_left, polar_sub_left, polar_smul_left, smul_eq_mul, polar_vec_vec,
    Bool.not_not, hij, Ne.symm hij, false_and, true_and, Bool.eq_not_self, ite_false, ite_true,
    and_self]
  have hτ : (τ : K) ≠ 0 := τ.ne_zero
  match_scalars <;> (try field_simp) <;> ring

theorem spinAction_longSL2_weylSL2_of_polar {i j : Fin n} (hij : i ≠ j) (s t : Bool) (τ : Kˣ)
    {v : V} (hi : ∀ r, polar Q v (F.vec i r) = 0) (hj : ∀ r, polar Q v (F.vec j r) = 0) :
    spinAction Q (F.longSL2 hij s t (weylSL2 τ)) v = v := by
  rw [spinAction_longSL2_weylSL2]
  simp [hi, hj]

theorem spinAction_longTorus {i j : Fin n} (hij : i ≠ j) (s t : Bool) (τ : Kˣ) (v : V) :
    spinAction Q (F.longTorus hij s t τ) v =
      v + ((τ : K) - 1) • (polar Q v (F.vec i (!s)) • F.vec i s + polar Q v (F.vec j (!t)) • F.vec j t)
        + (((τ⁻¹ : Kˣ) : K) - 1) •
          (polar Q v (F.vec i s) • F.vec i (!s) + polar Q v (F.vec j t) • F.vec j (!t)) := by
  rw [longTorus_apply, diagSL2_eq, map_mul, map_mul, LinearEquiv.mul_apply,
    spinAction_longSL2_weylSL2, spinAction_longSL2_weylSL2]
  simp only [polar_add_left, polar_sub_left, polar_smul_left, smul_eq_mul, polar_vec_vec,
    Bool.not_not, hij, Ne.symm hij, false_and, true_and, Bool.eq_not_self, ite_false, ite_true,
    and_self]
  have hτ : (τ : K) ≠ 0 := τ.ne_zero
  match_scalars <;> (try field_simp) <;> simp <;> ring

theorem spinAction_longWeyl {i j : Fin n} (hij : i ≠ j) (s t : Bool) (v : V) :
    spinAction Q (F.longWeyl hij s t) v =
      v + (polar Q v (F.vec j t) - polar Q v (F.vec i (!s))) • F.vec i s
        + (polar Q v (F.vec j (!t)) - polar Q v (F.vec i s)) • F.vec i (!s)
        - (polar Q v (F.vec j (!t)) + polar Q v (F.vec i s)) • F.vec j t
        - (polar Q v (F.vec j t) + polar Q v (F.vec i (!s))) • F.vec j (!t) := by
  rw [longWeyl, spinAction_longSL2_weylSL2]
  simp

theorem spinAction_longWeyl_of_polar {i j : Fin n} (hij : i ≠ j) (s t : Bool) {v : V}
    (hi : ∀ r, polar Q v (F.vec i r) = 0) (hj : ∀ r, polar Q v (F.vec j r) = 0) :
    spinAction Q (F.longWeyl hij s t) v = v :=
  F.spinAction_longSL2_weylSL2_of_polar hij s t 1 hi hj

@[simp]
theorem spinAction_longWeyl_vec_left {i j : Fin n} (hij : i ≠ j) (s t : Bool) :
    spinAction Q (F.longWeyl hij s t) (F.vec i s) = -F.vec j (!t) := by
  rw [spinAction_longWeyl]
  simp [polar_vec_vec, hij]

@[simp]
theorem spinAction_longWeyl_vec_left_not {i j : Fin n} (hij : i ≠ j) (s t : Bool) :
    spinAction Q (F.longWeyl hij s t) (F.vec i (!s)) = -F.vec j t := by
  rw [spinAction_longWeyl]
  simp [polar_vec_vec, hij]

@[simp]
theorem spinAction_longWeyl_vec_right {i j : Fin n} (hij : i ≠ j) (s t : Bool) :
    spinAction Q (F.longWeyl hij s t) (F.vec j t) = F.vec i (!s) := by
  rw [spinAction_longWeyl]
  simp [polar_vec_vec, Ne.symm hij]

@[simp]
theorem spinAction_longWeyl_vec_right_not {i j : Fin n} (hij : i ≠ j) (s t : Bool) :
    spinAction Q (F.longWeyl hij s t) (F.vec j (!t)) = F.vec i s := by
  rw [spinAction_longWeyl]
  simp [polar_vec_vec, Ne.symm hij]

theorem spinAction_longWeyl_vec_of_ne {i j : Fin n} (hij : i ≠ j) (s t : Bool) {k : Fin n}
    (hki : k ≠ i) (hkj : k ≠ j) (u : Bool) :
    spinAction Q (F.longWeyl hij s t) (F.vec k u) = F.vec k u :=
  F.spinAction_longWeyl_of_polar hij s t (fun r => F.polar_vec_of_ne hki u r)
    (fun r => F.polar_vec_of_ne hkj u r)

end HypFrame

@[expose] def longWeylBool {n : ℕ} (i j : Fin n) (s t : Bool) (m : Fin n) (r : Bool) : Bool :=
  if m = i ∨ m = j then xor r (xor s (!t)) else r

@[expose] def longWeylSign {n : ℕ} (i m : Fin n) : K := if m = i then -1 else 1

@[expose] def longCoroot {n : ℕ} (i j : Fin n) (s t : Bool) (m : Fin n) (r : Bool) : ℤ :=
  (if m = i then (if r = s then 1 else -1) else 0) + (if m = j then (if r = t then 1 else -1) else 0)

section LongWeylLabels

variable {n : ℕ} {i j : Fin n} (s t : Bool)

@[simp] theorem longWeylBool_left : longWeylBool i j s t i s = !t := by
  cases s <;> cases t <;> simp [longWeylBool]

@[simp] theorem longWeylBool_left_not : longWeylBool i j s t i (!s) = t := by
  cases s <;> cases t <;> simp [longWeylBool]

@[simp] theorem longWeylBool_right : longWeylBool i j s t j t = !s := by
  cases s <;> cases t <;> simp [longWeylBool]

@[simp] theorem longWeylBool_right_not : longWeylBool i j s t j (!t) = s := by
  cases s <;> cases t <;> simp [longWeylBool]

theorem longWeylBool_of_ne {m : Fin n} (hmi : m ≠ i) (hmj : m ≠ j) (r : Bool) :
    longWeylBool i j s t m r = r := by
  simp [longWeylBool, hmi, hmj]

@[simp] theorem longWeylSign_self : (longWeylSign i i : K) = -1 := by simp [longWeylSign]

theorem longWeylSign_of_ne {m : Fin n} (hmi : m ≠ i) : (longWeylSign i m : K) = 1 := by
  simp [longWeylSign, hmi]

end LongWeylLabels

theorem longCoroot_not {n : ℕ} (i j : Fin n) (s t : Bool) (m : Fin n) (r : Bool) :
    longCoroot i j s t m (!r) = -longCoroot i j s t m r := by
  simp only [longCoroot]
  by_cases hi : m = i <;> by_cases hj : m = j <;> cases r <;> cases s <;> cases t <;>
    simp [hi, hj] <;> omega

namespace HypFrame

variable (F : HypFrame Q n)

theorem spinAction_longWeyl_vec {i j : Fin n} (hij : i ≠ j) (s t : Bool) (m : Fin n) (r : Bool) :
    spinAction Q (F.longWeyl hij s t) (F.vec m r) =
      (longWeylSign i m : K) • F.vec (Equiv.swap i j m) (longWeylBool i j s t m r) := by
  by_cases hmi : m = i
  · subst hmi
    rcases Bool.eq_or_eq_not r s with rfl | rfl
    · simp
    · simp
  · by_cases hmj : m = j
    · subst hmj
      rw [longWeylSign_of_ne hmi, one_smul, Equiv.swap_apply_right]
      rcases Bool.eq_or_eq_not r t with rfl | rfl
      · simp
      · simp
    · rw [F.spinAction_longWeyl_vec_of_ne hij s t hmi hmj, longWeylSign_of_ne hmi,
        longWeylBool_of_ne s t hmi hmj, Equiv.swap_apply_of_ne_of_ne hmi hmj, one_smul]

theorem longWeyl_conj_longRoot {i j : Fin n} (hij : i ≠ j) (s t : Bool) {k l : Fin n}
    (hkl : k ≠ l) (u v : Bool) (c : K) :
    F.longWeyl hij s t * F.longRoot hkl u v (.ofAdd c) * (F.longWeyl hij s t)⁻¹ =
      F.longRoot ((Equiv.swap i j).injective.ne hkl) (longWeylBool i j s t k u)
        (longWeylBool i j s t l v) (.ofAdd ((longWeylSign i k : K) * longWeylSign i l * c)) :=
  F.conj_longRoot _ hkl u v _ _ _ (F.spinAction_longWeyl_vec hij s t k u)
    (F.spinAction_longWeyl_vec hij s t l v) c

theorem spinAction_longTorus_vec {i j : Fin n} (hij : i ≠ j) (s t : Bool) (τ : Kˣ) (m : Fin n)
    (r : Bool) :
    spinAction Q (F.longTorus hij s t τ) (F.vec m r) =
      ((τ ^ longCoroot i j s t m r : Kˣ) : K) • F.vec m r := by
  rw [spinAction_longTorus]
  by_cases hmi : m = i
  · subst hmi
    rcases Bool.eq_or_eq_not r s with rfl | rfl
    · simp [longCoroot, polar_vec_vec, hij]
      module
    · simp [longCoroot, polar_vec_vec, hij]
      module
  · by_cases hmj : m = j
    · subst hmj
      rcases Bool.eq_or_eq_not r t with rfl | rfl
      · simp [longCoroot, polar_vec_vec, hmi]
        module
      · simp [longCoroot, polar_vec_vec, hmi]
        module
    · simp [longCoroot, polar_vec_vec, hmi, hmj]

theorem longTorus_conj_longRoot {i j : Fin n} (hij : i ≠ j) (s t : Bool) (τ : Kˣ) {k l : Fin n}
    (hkl : k ≠ l) (u v : Bool) (c : K) :
    F.longTorus hij s t τ * F.longRoot hkl u v (.ofAdd c) * (F.longTorus hij s t τ)⁻¹ =
      F.longRoot hkl u v
        (.ofAdd (((τ ^ (longCoroot i j s t k u + longCoroot i j s t l v) : Kˣ) : K) * c)) := by
  rw [F.conj_longRoot _ hkl u v hkl u v (F.spinAction_longTorus_vec hij s t τ k u)
    (F.spinAction_longTorus_vec hij s t τ l v) c, zpow_add, Units.val_mul]

@[expose] noncomputable def numOp (m : Fin n) (r : Bool) : CliffordAlgebra Q :=
  ι Q (F.vec m r) * ι Q (F.vec m (!r))

theorem commute_numOp (m : Fin n) (r : Bool) (m' : Fin n) (r' : Bool) :
    Commute (F.numOp m r) (F.numOp m' r') := by
  by_cases hm : m = m'
  · subst hm
    rcases Bool.eq_or_eq_not r' r with rfl | rfl
    · exact Commute.refl _
    · have h1 : F.numOp m r * F.numOp m (!r) = 0 := by
        simp only [numOp, mul_assoc, F.ι_vec_mul_ι_vec_self_mul, mul_zero]
      have h2 : F.numOp m (!r) * F.numOp m r = 0 := by
        simp only [numOp, Bool.not_not, mul_assoc, F.ι_vec_mul_ι_vec_self_mul, mul_zero]
      change _ * _ = _ * _
      rw [h1, h2]
  · exact commute_ι_mul_ι Q (F.polar_vec_of_ne hm r r') (F.polar_vec_of_ne hm r (!r'))
      (F.polar_vec_of_ne hm (!r) r') (F.polar_vec_of_ne hm (!r) (!r'))

theorem longPair_X_mul_Y {i j : Fin n} (hij : i ≠ j) (s t : Bool) :
    (F.longPair hij s t).X * (F.longPair hij s t).Y = F.numOp j t * F.numOp i s := by
  simp only [longPair, numOp, mul_assoc]
  exact ι_mul_ι_mul_ι_mul_comm Q (F.polar_vec_of_ne hij s t) (F.polar_vec_of_ne hij s (!t)) _

theorem longPair_Y_mul_X {i j : Fin n} (hij : i ≠ j) (s t : Bool) :
    (F.longPair hij s t).Y * (F.longPair hij s t).X = F.numOp i (!s) * F.numOp j (!t) := by
  simp only [longPair, numOp, Bool.not_not, mul_assoc]
  exact ι_mul_ι_mul_ι_mul_comm Q (F.polar_vec_of_ne hij.symm (!t) (!s))
    (F.polar_vec_of_ne hij.symm (!t) s) _

theorem coe_longTorus {i j : Fin n} (hij : i ≠ j) (s t : Bool) (τ : Kˣ) :
    (F.longTorus hij s t τ : CliffordAlgebra Q) =
      (F.longPair hij s t).toFun ((diagSL2 τ : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) := rfl

theorem commute_longTorus_numOp {i j : Fin n} (hij : i ≠ j) (s t : Bool) (τ : Kˣ) (m : Fin n)
    (r : Bool) : Commute (F.longTorus hij s t τ : CliffordAlgebra Q) (F.numOp m r) := by
  rw [coe_longTorus]
  refine SL2Pair.commute_toFun_diagSL2 _ ?_ ?_ τ
  · rw [longPair_X_mul_Y]
    exact (F.commute_numOp _ _ _ _).mul_left (F.commute_numOp _ _ _ _)
  · rw [longPair_Y_mul_X]
    exact (F.commute_numOp _ _ _ _).mul_left (F.commute_numOp _ _ _ _)

theorem commute_longTorus_longTorus {i j : Fin n} (hij : i ≠ j) (s t : Bool) (τ : Kˣ)
    {k l : Fin n} (hkl : k ≠ l) (u v : Bool) (σ : Kˣ) :
    Commute (F.longTorus hij s t τ) (F.longTorus hkl u v σ) := by
  refine commute_of_coe ?_
  rw [F.coe_longTorus hkl]
  refine (SL2Pair.commute_toFun_diagSL2 _ ?_ ?_ σ).symm
  · rw [longPair_X_mul_Y]
    exact ((F.commute_longTorus_numOp hij s t τ _ _).mul_right
      (F.commute_longTorus_numOp hij s t τ _ _)).symm
  · rw [longPair_Y_mul_X]
    exact ((F.commute_longTorus_numOp hij s t τ _ _).mul_right
      (F.commute_longTorus_numOp hij s t τ _ _)).symm

end HypFrame

end CFSG.LieType.Universal.Spin
